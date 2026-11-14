-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb42_original_finite_negative_mark_times_terminal_margin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:31:20.719505+00:00
-- url     : https://prove2.me/submissions/9bfa7681-7424-4489-86ab-b3c6bb4b8ad2

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Theorems.Thm_AvramDividend_Classical_avram_bva51_finite_count_mark_times_real_finset
import Theorems.Thm_AvramDividend_Classical_avram_bva41_finite_distinct_mark_times_positive_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite original physical jump times avoid a deterministic terminal time by a
strict last-strip margin whenever there is no jump at that terminal time. -/
theorem solution
    (S : Set ℝ≥0)
    (hCount : (Measure.count S) < ⊤)
    (T : ℝ) (hT : 0 ≤ T)
    (hNoTerminal : (⟨T,hT⟩ : ℝ≥0) ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ≥0, t ∈ S → (t : ℝ) ≤ T → (t : ℝ) ≤ T - δ := by
  classical
  obtain ⟨F, hF⟩ :=
    avram_bva51_finite_count_mark_times_real_finset S hCount
  have hTnot : T ∉ F := by
    intro hTF
    apply hNoTerminal
    apply (hF ⟨T,hT⟩).2
    change T ∈ F
    exact hTF
  obtain ⟨δ,hδ,hgap⟩ :=
    avram_bva41_finite_distinct_mark_times_positive_gap (insert T F)
  refine ⟨δ,hδ,?_⟩
  intro t ht htT
  have htF : (t : ℝ) ∈ F := (hF t).1 ht
  have htNe : (t : ℝ) ≠ T := by
    intro heq
    apply hTnot
    simpa [heq] using htF
  have hsep : δ ≤ |(t : ℝ) - T| :=
    hgap (t : ℝ) (Finset.mem_insert_of_mem htF) T
      (Finset.mem_insert_self T F) htNe
  have hdiff : |(t : ℝ) - T| = T - (t : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr htT)]
    ring
  linarith
