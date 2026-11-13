-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_original_all_reciprocal_jump_levels_absent_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:05:40.720019+00:00
-- url     : https://prove2.me/submissions/0e826ce7-cc57-4e26-82a0-67fc18b73590

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b20_original_countable_reciprocal_mark_levels_null
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n k : ℕ) (v : ℝ≥0),
      0 < v → v ≤ (n : ℝ≥0) →
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω ≠
        (1 / ((k : ℝ) + 1)) := by
  filter_upwards
    [avram_b20_original_countable_reciprocal_mark_levels_null X hX hBV]
    with ω hω
  intro n k v hv hvn heq
  let A : Set (ℝ≥0 × ℝ) := Ioc 0 (n : ℝ≥0) ×ˢ
    ({-(1 / ((k : ℝ) + 1))} : Set ℝ)
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
  have hsubset : A ⊆
      (⋃ p : ℕ × ℕ,
        Ioc (0 : ℝ≥0) (p.1 : ℝ≥0) ×ˢ
          ({-(1 / ((p.2 : ℝ) + 1))} : Set ℝ)) := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨(n, k), hz⟩
  have hzero : NX A = 0 := by
    apply le_antisymm _ bot_le
    calc
      NX A ≤ NX (⋃ p : ℕ × ℕ,
          Ioc (0 : ℝ≥0) (p.1 : ℝ≥0) ×ˢ
          ({-(1 / ((p.2 : ℝ) + 1))} : Set ℝ)) :=
        measure_mono hsubset
      _ = 0 := hω
  have hcount :=
    avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
      X ω A (measurableSet_Ioc.prod (measurableSet_singleton _))
  change NX A = ({u : ℝ≥0 | 0 < u ∧
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0 ∧
    (u, X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) ∈ A}).encard
      at hcount
  rw [hzero] at hcount
  have hEmpty := Set.encard_eq_zero.mp ((ENat.toENNReal_eq_zero).mp hcount.symm)
  have ha : 0 < (1 / ((k : ℝ) + 1)) := by positivity
  have hj : X.X v ω -
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v =
      -(1 / ((k : ℝ) + 1)) := by
    linear_combination -heq
  have hmem : v ∈ {u : ℝ≥0 | 0 < u ∧
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0 ∧
    (u, X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) ∈ A} := by
    refine ⟨hv, ?_, ?_⟩
    · rw [hj]
      exact ne_of_lt (neg_lt_zero.mpr ha)
    · exact ⟨⟨hv, hvn⟩, hj⟩
  rw [hEmpty] at hmem
  simpa using hmem
