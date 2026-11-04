-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:14:39.383391+00:00
-- url     : https://prove2.me/submissions/8554db75-f5c1-4ae3-a405-90ab0ab6588f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_large_increments_impossible
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Every persistently large shrinking ordered cell sequence admits a
cofinal subsequence crossing its genuine jump in the right-closed sense. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ∃ φ : ℕ → ℕ,
      Tendsto φ atTop (atTop : Filter ℕ) ∧
      (∀ n, a (φ n) < t ∧ t ≤ b (φ n)) ∧
      ρ ≤ |Y t - Function.leftLim Y t| := by
  obtain ⟨φ, hφ, haφ, hbφ, hcases⟩ :=
    avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
      a b t hab ha hb
  have hlargeφ : ∀ n : ℕ,
      ρ ≤ |Y (b (φ n)) - Y (a (φ n))| :=
    fun n => hlarge (φ n)
  rcases hcases with hleft | hright | hcross
  · have hla : ∀ n, a (φ n) < t := by
      intro n
      exact lt_of_le_of_lt (hab (φ n)) (hleft n)
    have hsl : Tendsto (a ∘ φ) atTop (𝓝[<] t) ∧
        Tendsto (b ∘ φ) atTop (𝓝[<] t) :=
      ⟨tendsto_nhdsWithin_iff.mpr
        ⟨haφ, Filter.Eventually.of_forall hla⟩,
       tendsto_nhdsWithin_iff.mpr
        ⟨hbφ, Filter.Eventually.of_forall hleft⟩⟩
    exact False.elim
      (avram_p2_h_cadlag_same_side_large_increments_impossible
        Y t (a ∘ φ) (b ∘ φ) hL hR ρ hρ hlargeφ (Or.inl hsl))
  · have hrb : ∀ n, t ≤ b (φ n) := by
      intro n
      exact le_trans (hright n) (hab (φ n))
    have hsr : Tendsto (a ∘ φ) atTop (nhdsWithin t (Ici t)) ∧
        Tendsto (b ∘ φ) atTop (nhdsWithin t (Ici t)) :=
      ⟨tendsto_nhdsWithin_iff.mpr
        ⟨haφ, Filter.Eventually.of_forall hright⟩,
       tendsto_nhdsWithin_iff.mpr
        ⟨hbφ, Filter.Eventually.of_forall hrb⟩⟩
    exact False.elim
      (avram_p2_h_cadlag_same_side_large_increments_impossible
        Y t (a ∘ φ) (b ∘ φ) hL hR ρ hρ hlargeφ (Or.inr hsr))
  · refine ⟨φ, hφ, hcross, ?_⟩
    have hal : Tendsto (a ∘ φ) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨haφ, Filter.Eventually.of_forall (fun n => (hcross n).1)⟩
    have hbr : Tendsto (b ∘ φ) atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hbφ, Filter.Eventually.of_forall (fun n => (hcross n).2)⟩
    exact avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump
      Y t (a ∘ φ) (b ∘ φ) hal hbr hL hR ρ hlargeφ
