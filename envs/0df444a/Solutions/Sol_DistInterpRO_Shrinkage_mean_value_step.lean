-- Prove2me | solution 1 for DistInterpRO.Shrinkage.mean_value_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:39:51.994565+00:00
-- url     : https://prove2.me/submissions/3d2f16b6-f95b-491c-87a3-81ba557b849e

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

theorem aux_mvs_hasDerivAt {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Differentiable ℝ F) (x₀ x₁ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x₀ + s • x₁)) (fderiv ℝ F (x₀ + t • x₁) x₁) t := by
  have h1 : HasDerivAt (fun s : ℝ => x₀ + s • x₁) x₁ t := by
    simpa using ((hasDerivAt_id t).smul_const x₁).const_add x₀
  have h2 := (hF (x₀ + t • x₁)).hasFDerivAt.comp_hasDerivAt t h1
  exact h2

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage
open MeasureTheory
open scoped Pointwise

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Differentiable ℝ (f v)) (x₀ x₁ : EuclideanSpace ℝ (Fin m)) :
    ∃ β ∈ Set.Icc (0 : ℝ) 1, f v (x₀ + x₁) = f v x₀ + fderiv ℝ (f v) (x₀ + β • x₁) x₁ := by
  have hd := aux_mvs_hasDerivAt (f v) hf x₀ x₁
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f v (x₀ + s • x₁))
    (fun t => fderiv ℝ (f v) (x₀ + t • x₁) x₁) (zero_lt_one' ℝ)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
  refine ⟨c, Set.Ioo_subset_Icc_self hc, ?_⟩
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hceq
  linarith
