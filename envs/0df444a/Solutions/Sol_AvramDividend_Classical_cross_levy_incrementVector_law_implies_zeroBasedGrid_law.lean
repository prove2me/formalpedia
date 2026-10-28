-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_incrementVector_law_implies_zeroBasedGrid_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:51:03.702286+00:00
-- url     : https://prove2.me/submissions/6e4a55e4-3d3c-4294-9597-9e61038329ef

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (n : ℕ)
    (hInc :
      Measure.map (fun ω : Ω₁ => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P₁ =
      Measure.map (fun ω : Ω₂ => fun i : Fin n =>
        Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) P₂) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω) P₂ := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
    ∑ k ∈ Finset.range (i.val + 1), (if h : k < n then v ⟨k, h⟩ else 0)
  have hg : Measurable g := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ => ?_
    by_cases h : k < n
    · simp only [h, dif_pos]; exact measurable_pi_apply _
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  have keyX : (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω) =
      g ∘ (fun ω : Ω₁ => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) := by
    funext ω i
    simp only [Function.comp, g]
    calc
      X.X (t (i.val + 1)) ω =
          X.X (t (i.val + 1)) ω - X.X (t 0) ω := by
            simp only [ht0, X.X_zero, sub_zero]
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (X.X (t (k + 1)) ω - X.X (t k) ω) :=
            (chat04_all_n_levy_increment_telescoping X t (i.val + 1) ω).symm
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (if h : k < n then X.X (t (k + 1)) ω - X.X (t k) ω else 0) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk' : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt
            rw [dif_pos hk']
  have keyY : (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω) =
      g ∘ (fun ω : Ω₂ => fun i : Fin n =>
        Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) := by
    funext ω i
    simp only [Function.comp, g]
    calc
      Y.X (t (i.val + 1)) ω =
          Y.X (t (i.val + 1)) ω - Y.X (t 0) ω := by
            simp only [ht0, Y.X_zero, sub_zero]
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (Y.X (t (k + 1)) ω - Y.X (t k) ω) :=
            (chat04_all_n_levy_increment_telescoping Y t (i.val + 1) ω).symm
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (if h : k < n then Y.X (t (k + 1)) ω - Y.X (t k) ω else 0) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk' : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt
            rw [dif_pos hk']
  have hmX : Measurable (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) :=
    measurable_pi_lambda _ fun i =>
      (X.adapted.measurable).sub (X.adapted.measurable)
  have hmY : Measurable (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) :=
    measurable_pi_lambda _ fun i =>
      (Y.adapted.measurable).sub (Y.adapted.measurable)
  rw [keyX, keyY, ← Measure.map_map hg hmX, ← Measure.map_map hg hmY]
  exact congrArg (Measure.map g) hInc
