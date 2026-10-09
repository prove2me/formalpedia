-- Prove2me | solution 1 for GaussianMatrix.ou_semigroup_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:21:41.403425+00:00
-- url     : https://prove2.me/submissions/02938562-e07c-4b07-8bc2-690ca8b5dc34

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The image of `γ ⊗ γ` under `(x, y) ↦ a x + b y` is `γ` when `a² + b² = 1`. -/
lemma map_lin_comb_gaussian (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = gaussianReal 0 1 := by
  have h1 : (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x => a * x) (fun y => b * y) := by
    ext p; simp
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  rw [← Measure.conv, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · apply NNReal.eq; simp [hab]

lemma integral_lin_comb_gaussian (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ x, (∫ y, h (a * x + b * y) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  have hmap : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2) = gaussianReal 0 1 := by
    exact map_lin_comb_gaussian a b hab
  have hF : AEMeasurable (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by fun_prop
  have hh' : Integrable h (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2)) := by rw [hmap]; exact hh
  have hcomp : Integrable (fun p : ℝ × ℝ => h (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_map_measure hh'.aestronglyMeasurable hF).1 hh'
  rw [← integral_prod (fun p : ℝ × ℝ => h (a * p.1 + b * p.2)) hcomp]
  rw [← integral_map hF (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

end GaussianMatrix

open GaussianMatrix

theorem solution (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, (∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  apply integral_lin_comb_gaussian h hh
  have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.sq_sqrt (by linarith), sq, ← Real.exp_add]
  ring_nf
