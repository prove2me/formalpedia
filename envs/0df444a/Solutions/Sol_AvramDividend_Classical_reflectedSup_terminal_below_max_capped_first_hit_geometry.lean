-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_terminal_below_max_capped_first_hit_geometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:50:07.21298+00:00
-- url     : https://prove2.me/submissions/a0ab3efd-8eef-4b97-87ed-beb206689c7b

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_sup_level_hit_before_lower_endpoint
import Theorems.Thm_AvramDividend_Classical_first_exact_level_hit_of_upperSemicontinuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_nnreal_sInf_union_cap_eq_of_early_member

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (H : ℝ≥0) (x : ℝ) (hx : 0 < x)
    (hMax : sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = x)
    (hEnd : reflectedSup X H ω < x) :
    sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) < H ∧
    reflectedSup X (sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω = x ∧
    ∀ t : ℝ≥0, t ≤ H → reflectedSup X t ω ≤ x := by
  set R : ℝ≥0 → ℝ := fun u => reflectedSup X u ω with hR
  have husc := reflectedSup_upperSemicontinuousOn_Icc X ω H
  have hbdd : BddAbove (R '' Icc 0 H) := husc.bddAbove_of_isCompact isCompact_Icc
  have hBound : ∀ t : ℝ≥0, t ≤ H → R t ≤ x := fun t ht => by
    rw [← hMax]; exact le_csSup hbdd ⟨t, ⟨zero_le, ht⟩, rfl⟩
  obtain ⟨t0, ht0, hR0⟩ := usc_compact_sup_level_hit_before_lower_endpoint R H x husc hMax hEnd
  obtain ⟨T, hT, -, hTH, hRT, -⟩ := first_exact_level_hit_of_upperSemicontinuous R H x husc
    (reflectedSup_origin_eq_zero X ω) hx hBound ⟨t0, ht0, hR0.ge⟩
  have hcap := nnreal_sInf_union_cap_eq_of_early_member (Icc (0 : ℝ≥0) H ∩ R ⁻¹' Ici x) H
    ⟨T, ⟨⟨zero_le, hTH.le⟩, by simp [hRT]⟩, hTH.le⟩
  rw [hcap, ← hT]
  exact ⟨hTH, hRT, hBound⟩
