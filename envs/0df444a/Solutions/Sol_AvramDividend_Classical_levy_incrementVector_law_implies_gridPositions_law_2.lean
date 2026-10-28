-- Prove2me | solution 2 for AvramDividend.Classical.levy_incrementVector_law_implies_gridPositions_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:55:22.888817+00:00
-- url     : https://prove2.me/submissions/7fbf1cb1-d033-4004-a290-788398b22460

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ)
    (hLaw :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t 0) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t 0) ω) P := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
    ∑ k ∈ Finset.range (i.val + 1), (if h : k < n then v ⟨k, h⟩ else 0)
  have hg : Measurable g := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ => ?_
    by_cases h : k < n
    · simp only [h, dif_pos]; exact measurable_pi_apply _
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  have key : ∀ u : ℕ → ℝ≥0, (fun ω : Ω => fun i : Fin n => X.X (u (i.val + 1)) ω - X.X (u 0) ω) =
      g ∘ (fun ω : Ω => fun i : Fin n => X.X (u (i.val + 1)) ω - X.X (u i.val) ω) := by
    intro u
    funext ω i
    simp only [Function.comp, g]
    rw [← AvramDividend.Classical.chat04_all_n_levy_increment_telescoping X u (i.val + 1) ω]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt
    rw [dif_pos hk']
  have e1 := key (fun k => s + t k)
  have e2 := key t
  have hX : ∀ r : ℝ≥0, Measurable (X.X r) := fun r =>
    (X.adapted r).mono (𝓕.le r) le_rfl
  have hm : ∀ u : ℕ → ℝ≥0, Measurable
      (fun ω : Ω => fun i : Fin n => X.X (u (i.val + 1)) ω - X.X (u i.val) ω) := fun u =>
    measurable_pi_lambda _ fun i => (hX _).sub (hX _)
  rw [e1, e2, ← Measure.map_map hg (hm (fun k => s + t k)), ← Measure.map_map hg (hm t)]
  exact congrArg (Measure.map g) hLaw
