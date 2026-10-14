-- Prove2me | solution 1 for DbarRegularity.cauchyRiemann_lp_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:42:28.136534+00:00
-- url     : https://prove2.me/submissions/e65a80f1-a0d3-462e-921f-27c12731447e

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_complex



namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- For `1 < p < ∞` and `n : ℕ` there is `A` such that every `C¹` map `φ : ℂ → ℂⁿ` with compact
support satisfies `‖φ_s‖_p + ‖φ_t‖_p ≤ A ‖∂̄φ‖_p`. -/
theorem cauchyRiemann_lp_euclidean_aux (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ 1 φ → HasCompactSupport φ →
      eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar φ) (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA⟩ := cauchyRiemann_lp_complex p hp
  refine ⟨n * A, fun φ hφ hφc => ?_⟩
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := ENNReal.one_le_ofReal.2 hp.le
  have hsplit : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ ≤ ∑ j, ‖v j‖ := by
    intro v
    have hv : v = ∑ j, EuclideanSpace.single j (v j) := by
      ext i; simp [EuclideanSpace.single_apply]
    calc ‖v‖ = ‖∑ j, EuclideanSpace.single j (v j)‖ := by rw [← hv]
      _ ≤ ∑ j, ‖EuclideanSpace.single j (v j)‖ := norm_sum_le _ _
      _ = ∑ j, ‖v j‖ := by simp
  have hc := hφ.continuous_fderiv (by norm_num)
  have hd := hφ.differentiable one_ne_zero
  -- components
  let L : Fin n → EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    fun j => (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ
  have hL : ∀ j v, L j v = v j := fun j v => rfl
  have hfd : ∀ j z v, fderiv ℝ (fun w => φ w j) z v = fderiv ℝ φ z v j := by
    intro j z v
    have := ((L j).hasFDerivAt.comp z (hd z).hasFDerivAt).fderiv
    exact congrArg (fun T => T v) this
  have hcomp : ∀ j, ContDiff ℝ 1 (fun w => φ w j) := fun j => (L j).contDiff.comp hφ
  have hcompc : ∀ j, HasCompactSupport (fun w => φ w j) := fun j =>
    hφc.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) => v j) (by simp)
  have hdbar : ∀ j, dbar (fun w => φ w j) = fun z => dbar φ z j := by
    intro j; funext z; simp [dbar, hfd]
  have hdb : ∀ j, eLpNorm (fun z => dbar φ z j) P volume ≤ eLpNorm (dbar φ) P volume := fun j =>
    eLpNorm_mono fun z => PiLp.norm_apply_le _ _
  have hj : ∀ j, eLpNorm (fun z => fderiv ℝ φ z 1 j) P volume
      + eLpNorm (fun z => fderiv ℝ φ z Complex.I j) P volume ≤ A * eLpNorm (dbar φ) P volume := by
    intro j
    have := hA _ (hcomp j) (hcompc j)
    simp only [hfd, hdbar j] at this
    exact this.trans (by gcongr; exact hdb j)
  -- vector bound from components
  have hvec : ∀ v : ℂ, eLpNorm (fun z => fderiv ℝ φ z v) P volume
      ≤ ∑ j, eLpNorm (fun z => fderiv ℝ φ z v j) P volume := by
    intro v
    have hm : ∀ j ∈ Finset.univ, AEStronglyMeasurable (fun z => ‖fderiv ℝ φ z v j‖) volume :=
      fun j _ => (by fun_prop : Continuous fun z => ‖fderiv ℝ φ z v j‖).aestronglyMeasurable
    calc eLpNorm (fun z => fderiv ℝ φ z v) P volume
        ≤ eLpNorm (∑ j, fun z => ‖fderiv ℝ φ z v j‖) P volume := by
          apply eLpNorm_mono_real
          intro z
          rw [Finset.sum_apply]
          exact hsplit _
      _ ≤ ∑ j, eLpNorm (fun z => ‖fderiv ℝ φ z v j‖) P volume := eLpNorm_sum_le hm hP1
      _ = ∑ j, eLpNorm (fun z => fderiv ℝ φ z v j) P volume := by
          simp only [eLpNorm_norm]
  calc eLpNorm (fun z => fderiv ℝ φ z 1) P volume
        + eLpNorm (fun z => fderiv ℝ φ z Complex.I) P volume
      ≤ ∑ j, (eLpNorm (fun z => fderiv ℝ φ z 1 j) P volume
          + eLpNorm (fun z => fderiv ℝ φ z Complex.I j) P volume) := by
        rw [Finset.sum_add_distrib]; exact add_le_add (hvec 1) (hvec _)
    _ ≤ ∑ _j : Fin n, (A : ℝ≥0∞) * eLpNorm (dbar φ) P volume := Finset.sum_le_sum fun j _ => hj j
    _ = ((n * A : ℝ≥0) : ℝ≥0∞) * eLpNorm (dbar φ) P volume := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem solution (n : ℕ) (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ 1 φ → HasCompactSupport φ →
      eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar φ) (ENNReal.ofReal p) volume :=
  cauchyRiemann_lp_euclidean_aux n p hp
