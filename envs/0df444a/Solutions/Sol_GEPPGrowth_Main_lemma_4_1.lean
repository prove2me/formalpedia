-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:38:14.999871+00:00
-- url     : https://prove2.me/submissions/9120119a-8e05-4616-ae6e-396fd11e4310

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_KLTNuclear_Lasso_gaussian_tail
open MeasureTheory ProbabilityTheory

theorem solution (t : ℝ) (ht : 0 < t) :
    GEPPGrowth.Main.prob (gaussianReal 0 1) {x | t ≤ |x|} ≤
      Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2) := by
  have hnull : gaussianReal 0 1 ({t, -t} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous 0 (by norm_num) ((Set.toFinite _).measure_zero _)
  have hsub : {x : ℝ | t ≤ |x|} ⊆ {y : ℝ | t < |y|} ∪ {t, -t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases hx.lt_or_eq with h | h
    · exact Or.inl h
    · right
      rcases abs_eq (le_of_lt ht) |>.1 h.symm with h' | h' <;> simp [h']
  have hle : gaussianReal 0 1 {x : ℝ | t ≤ |x|} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-(t ^ 2) / 2) / t) :=
    calc _ ≤ gaussianReal 0 1 ({y : ℝ | t < |y|} ∪ {t, -t}) := measure_mono hsub
      _ ≤ gaussianReal 0 1 {y : ℝ | t < |y|} + gaussianReal 0 1 ({t, -t} : Set ℝ) :=
          measure_union_le _ _
      _ ≤ _ := by rw [hnull, add_zero]; exact KLTNuclear.Lasso.gaussian_tail ht
  have hval : Real.sqrt (2 / Real.pi) * Real.exp (-(t ^ 2) / 2) / t =
      Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2) := by
    rw [Real.sqrt_div (by norm_num), neg_div]
    field_simp
  unfold GEPPGrowth.Main.prob
  rw [← hval]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle
