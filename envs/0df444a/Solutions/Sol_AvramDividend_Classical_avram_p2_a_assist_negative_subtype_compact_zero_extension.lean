-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_negative_subtype_compact_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:39:39.668726+00:00
-- url     : https://prove2.me/submissions/3f0b2b0a-e8d3-4aa7-a290-499cb3c5ec75

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_separated_from_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_zero_extension_support_subset_negative_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical

/-- A compact negative-subtype test extends to a compact ambient real test separated from zero. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Iio (0 : ℝ) ∧
      ∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x := by
  classical
  let g : ℝ → ℝ :=
    Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ)
      (fun x => f x) 0
  obtain ⟨hg, hc⟩ :=
    avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact f
  obtain ⟨ε, hε, hSep⟩ :=
    avram_p2_g_radon_compact_test_separated_from_zero f
  have hSupport : Function.support g ⊆ Iic (-ε) :=
    avram_p2_g_radon_zero_extension_support_subset_negative_band f ε hSep
  have hTopSupport : tsupport g ⊆ Iic (-ε) := by
    change closure (Function.support g) ⊆ Iic (-ε)
    exact closure_minimal hSupport isClosed_Iic
  refine ⟨g, hg, hc, ?_, ?_⟩
  · intro x hx
    exact lt_of_le_of_lt (hTopSupport hx) (neg_lt_zero.mpr hε)
  · intro x
    exact Function.extend_val_apply
      (p := fun z : ℝ => z < 0) (b := (x : ℝ)) x.property
