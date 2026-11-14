-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB51_original_C1_compact_derivative_attains_maximum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:47:10.858602+00:00
-- url     : https://prove2.me/submissions/46ab95d5-a876-45dc-8caf-111de3d52e15

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

/- Compact C1 derivative attainment on any closed positive reserve subinterval of its open smooth domain. -/
/- Current-checker revalidation after immutable candidate 36659 was refused as stale when CLI checker implementation changed. -/
theorem solution
    (w : ℝ → ℝ) (s : Set ℝ)
    (hsOpen : IsOpen s) (hwSmooth : ContDiffOn ℝ 1 w s)
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ s) :
    ∃ t ∈ Icc a b,
      ∀ r ∈ Icc a b, deriv w r ≤ deriv w t := by
  have hC : ContinuousOn (deriv w) (Icc a b) :=
    (hwSmooth.continuousOn_deriv_of_isOpen hsOpen (by norm_num)).mono hBand
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  obtain ⟨t, ht, hMax⟩ := isCompact_Icc.exists_isMaxOn hne hC
  exact ⟨t, ht, fun r hr => hMax hr⟩
