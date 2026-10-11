-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.gramWeyl_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:36.105984+00:00
-- url     : https://prove2.me/submissions/152e753f-5675-4e67-88c2-c62b42072d9c

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.gramWeyl_eq
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Theorems.Thm_BookProof_YangMillsAbelianEsa_triple_swap_prime
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {d N : ℕ} (v : Fin N → Fin d → ℝ)
    (T : Fin d → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ∑ i : Fin d, ∑ j : Fin d,
        ((((1 / 2 : ℝ) * ∑ m : Fin N, v m i * v m j : ℝ)) : ℂ) • weylProd (T i) (T j) p
      = ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin N,
          (∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) ((∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) p) := by

  have hL : ∑ i : Fin d, ∑ j : Fin d,
        ((((1 / 2 : ℝ) * ∑ m : Fin N, v m i * v m j : ℝ)) : ℂ) • weylProd (T i) (T j) p
      = ∑ i : Fin d, ∑ j : Fin d, ∑ m : Fin N,
          (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ))
            • weylProd (T i) (T j) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hc : ((((1 / 2 : ℝ) * ∑ m : Fin N, v m i * v m j : ℝ)) : ℂ)
        = ∑ m : Fin N, (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hc, Finset.sum_smul]
  rw [hL, triple_swap_prime, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- the Weyl symmetrization is absorbed by the symmetry of the coefficients
  have hexp : (∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i)
        ((∑ i : Fin d, ((v m i : ℝ) : ℂ) • T i) p)
      = ∑ i : Fin d, ∑ j : Fin d,
          (((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T i (T j p) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  have hweyl : ∀ i j : Fin d,
      (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • weylProd (T i) (T j) p
        = ((1 / 2 : ℝ) : ℂ)
            • ((((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T i (T j p))
          + ((1 / 2 : ℝ) : ℂ)
            • ((((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T j (T i p)) := by
    intro i j
    simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      smul_add, smul_smul]
    congr 1 <;> (congr 1; push_cast; ring)
  have hA : ∑ i : Fin d, ∑ j : Fin d,
        (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • weylProd (T i) (T j) p
      = ((1 / 2 : ℝ) : ℂ) • ((∑ i : Fin d, ∑ j : Fin d,
            (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T i (T j p))
          + ∑ i : Fin d, ∑ j : Fin d,
            (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T j (T i p)) := by
    rw [smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hweyl i j
  have hswap : ∑ i : Fin d, ∑ j : Fin d,
        (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T j (T i p)
      = ∑ i : Fin d, ∑ j : Fin d,
        (((1 / 2 : ℝ) : ℂ) * ((v m i : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)) • T i (T j p) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  rw [hA, hswap, hexp]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]
  congr 1
  push_cast
  ring
