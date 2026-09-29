-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.polyGaussCoreT_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:21.186503+00:00
-- url     : https://prove2.me/submissions/5b2231b4-a6d4-41f5-8f7b-ae6a5b01863b

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.polyGaussCoreT_dense
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_phaseFun_ne_zero
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgLpT_mem_coreT
import Theorems.Thm_BookProof_ShiftedHermiteCore_inner_pgLpT_left
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) :
    Dense ((polyGaussCoreT a k : Submodule ℂ (L2d d)) : Set (L2d d)) := by

  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hu2 : MemLp (u : Vd d → ℂ) 2 (volume : Measure (Vd d)) := Lp.memLp u
  have hshift : MemLp (fun y : Vd d => (u : Vd d → ℂ) (y + a)) 2 (volume : Measure (Vd d)) :=
    hu2.comp_measurePreserving (measurePreserving_add_right (volume : Measure (Vd d)) a)
  set w : Vd d → ℂ :=
    fun y => (starRingEnd ℂ) (phaseFun k (y + a)) * (u : Vd d → ℂ) (y + a) with hwdef
  have hwnorm : ∀ y : Vd d, ‖w y‖ = ‖(u : Vd d → ℂ) (y + a)‖ := by
    intro y
    rw [hwdef]
    simp [norm_phaseFun]
  have hwLp : MemLp w 2 (volume : Measure (Vd d)) := by
    refine hshift.mono ?_ (Filter.Eventually.of_forall fun y => (hwnorm y).le)
    have hphase : Continuous fun y : Vd d => (starRingEnd ℂ) (phaseFun k (y + a)) :=
      Complex.continuous_conj.comp
        ((continuous_phaseFun k).comp (continuous_id.add continuous_const))
    exact hphase.aestronglyMeasurable.mul hshift.1
  have hmon : ∀ α : Fin d →₀ ℕ, ∫ y : Vd d, pgFun (monomial α (1 : ℂ)) y * w y = 0 := by
    intro α
    have h0 : (inner ℂ (pgLpT a k (monomial α (1 : ℂ))) u : ℂ) = 0 :=
      hu _ (pgLpT_mem_coreT a k _)
    rw [inner_pgLpT_left] at h0
    have hsub : ∫ x : Vd d,
          (starRingEnd ℂ) (pgFunT a k (monomial α (1 : ℂ)) x) * (u : Vd d → ℂ) x
        = ∫ y : Vd d,
          (starRingEnd ℂ) (pgFunT a k (monomial α (1 : ℂ)) (y + a))
            * (u : Vd d → ℂ) (y + a) :=
      (integral_add_right_eq_self
        (fun x : Vd d =>
          (starRingEnd ℂ) (pgFunT a k (monomial α (1 : ℂ)) x) * (u : Vd d → ℂ) x) a).symm
    rw [hsub] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [pgFunT, hwdef, add_sub_cancel_right, map_mul]
    rw [conj_pgFun_monomial_one]
    ring
  have hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ y : Vd d, pgFun p y * w y = 0 := by
    intro p
    have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
      (MvPolynomial.support_sum_monomial_coeff p).symm
    have hpt : ∀ y : Vd d, pgFun p y * w y
        = ∑ v ∈ p.support, MvPolynomial.coeff v p * (pgFun (monomial v (1 : ℂ)) y * w y) := by
      intro y
      rw [pgFun]
      nth_rewrite 1 [hsum]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [pgFun, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun v _ =>
      ((integrable_mul_of_memLp_two (memLp_pgFun (monomial v (1 : ℂ))) hwLp)).const_mul _)]
    simp [integral_const_mul, hmon]
  have hzero := ae_eq_zero_of_moments hwLp hmom
  have hua : ∀ᵐ y : Vd d, (u : Vd d → ℂ) (y + a) = 0 := by
    filter_upwards [hzero] with y hy
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd ((starRingEnd ℂ).injective (by simpa using h)) (phaseFun_ne_zero k (y + a))
    · exact h
  have hinner : (inner ℂ u u : ℂ) = 0 := by
    rw [L2.inner_def]
    rw [← integral_add_right_eq_self
      (fun x : Vd d => (inner ℂ ((u : Vd d → ℂ) x) ((u : Vd d → ℂ) x) : ℂ)) a]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hua] with y hy
    simp [hy]
  exact inner_self_eq_zero.mp hinner
