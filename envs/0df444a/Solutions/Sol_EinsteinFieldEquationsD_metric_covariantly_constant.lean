-- Prove2me | solution 1 for EinsteinFieldEquationsD.metric_covariantly_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:43:07.889142+00:00
-- url     : https://prove2.me/submissions/45c004ea-0502-4a6c-b9f2-f0566f1a4384

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic.Ring
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD
open scoped Topology

theorem solution {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ l a b : Fin D, covDeriv2 g g x l a b = 0 := by
  classical
  intro x hx l a b
  let P (i j k : Fin D) : ℝ := partialDeriv i (fun y => g y j k) x
  let Q (i j k : Fin D) : ℝ := P i k j + P j k i - P k i j
  have hpart (i j k : Fin D) : P i j k = P i k j := by
    have hU : ∀ᶠ y in 𝓝 x, y ∈ U := hg.isOpen.mem_nhds hx
    have hlocal : (fun y => g y j k) =ᶠ[𝓝 x] (fun y => g y k j) :=
      hU.mono (fun y hy => hg.symm y hy j k)
    change fderiv ℝ (fun y => g y j k) x (Pi.single i 1) =
      fderiv ℝ (fun y => g y k j) x (Pi.single i 1)
    rw [hlocal.fderiv_eq]
  have hmat : Matrix.transpose (g x) = g x := by
    ext i j
    exact hg.symm x hx j i
  have hinvSymm : Matrix.transpose ((g x)⁻¹) = (g x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hmat]
  have hinvSymmComp (i j : Fin D) :
      (g x)⁻¹ i j = (g x)⁻¹ j i := by
    have hh := congrArg (fun A : Matrix (Fin D) (Fin D) ℝ => A j i) hinvSymm
    simpa [Matrix.transpose_apply] using hh
  have hdet : IsUnit (g x).det :=
    isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx)
  have hmulinverse : (g x)⁻¹ * g x =
      (1 : Matrix (Fin D) (Fin D) ℝ) :=
    Matrix.nonsing_inv_mul (g x) hdet
  have hInv (t j : Fin D) :
      (∑ s : Fin D, invMetric g x s t * g x s j) =
        if t = j then 1 else 0 := by
    calc
      _ = ∑ s : Fin D, (g x)⁻¹ t s * g x s j := by
        apply Finset.sum_congr rfl
        intro s _
        change (g x)⁻¹ s t * g x s j =
          (g x)⁻¹ t s * g x s j
        rw [hinvSymmComp s t]
      _ = ((g x)⁻¹ * g x) t j := by rw [Matrix.mul_apply]
      _ = (1 : Matrix (Fin D) (Fin D) ℝ) t j := by rw [hmulinverse]
      _ = _ := by simp [Matrix.one_apply]
  have hpair (F : Fin D → ℝ) (j : Fin D) :
      (∑ s : Fin D, ((1 / 2 : ℝ) *
          ∑ t : Fin D, invMetric g x s t * F t) * g x s j) =
        (1 / 2 : ℝ) * F j := by
    calc
      _ = (1 / 2 : ℝ) *
          (∑ s : Fin D, ∑ t : Fin D,
            (invMetric g x s t * F t) * g x s j) := by
              simp only [Finset.mul_sum, Finset.sum_mul]
              ring
      _ = (1 / 2 : ℝ) *
          (∑ t : Fin D, ∑ s : Fin D,
            (invMetric g x s t * F t) * g x s j) := by
              rw [Finset.sum_comm]
      _ = (1 / 2 : ℝ) *
          (∑ t : Fin D,
            (∑ s : Fin D, invMetric g x s t * g x s j) * F t) := by
              congr 1
              apply Finset.sum_congr rfl
              intro t _
              simp only [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = (1 / 2 : ℝ) * F j := by
        simp_rw [hInv]
        simp
  have hΓ (s i j : Fin D) :
      christoffel g x s i j =
        (1 / 2 : ℝ) * ∑ t : Fin D,
          invMetric g x s t * Q i j t := by
    rfl
  have hΓ1 :
      (∑ s : Fin D, christoffel g x s l a * g x s b) =
      (1 / 2 : ℝ) * Q l a b := by
    simp_rw [hΓ]
    exact hpair (Q l a) b
  have hΓ2 :
      (∑ s : Fin D, christoffel g x s l b * g x a s) =
      (1 / 2 : ℝ) * Q l b a := by
    calc
      _ = ∑ s : Fin D, christoffel g x s l b * g x s a := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hg.symm x hx a s]
      _ = (1 / 2 : ℝ) * Q l b a := by
          simp_rw [hΓ]
          exact hpair (Q l b) a
  change P l a b -
    (∑ s : Fin D, (christoffel g x s l a * g x s b +
      christoffel g x s l b * g x a s)) = 0
  rw [Finset.sum_add_distrib, hΓ1, hΓ2]
  dsimp [Q]
  rw [hpart l b a, hpart a b l, hpart b a l]
  ring
