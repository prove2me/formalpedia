-- Prove2me | solution 1 for AvramDividend.Classical.usc_capped_first_closed_hit_le_iff_prefix_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:27:38.102159+00:00
-- url     : https://prove2.me/submissions/0bc7ff5b-6582-4647-9a57-f15ac56fe19c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (H t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 H))
    (ht : t < H) :
    sInf ((Icc (0 : ℝ≥0) H ∩ R ⁻¹' Ici x) ∪ {H}) ≤ t ↔
      ∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s := by
  let A : Set ℝ≥0 := (Icc (0 : ℝ≥0) H ∩ R ⁻¹' Ici x) ∪ {H}
  have hcomp : IsCompact A := by
    exact (UpperSemicontinuousOn.isCompact_inter_preimage_Ici
      husc isCompact_Icc x).union isCompact_singleton
  have hne : A.Nonempty := ⟨H, Or.inr rfl⟩
  have hmin : sInf A ∈ A := hcomp.sInf_mem hne
  have hbdd : BddBelow A :=
    ⟨0, by intro s hs; exact (show (0 : ℝ≥0) ≤ s from zero_le)⟩
  constructor
  · intro hT
    have hA : sInf A ∈ Icc (0 : ℝ≥0) H ∩ R ⁻¹' Ici x := by
      rcases hmin with hlev | hcap
      · exact hlev
      · have hEq : sInf A = H := by simpa only [Set.mem_singleton_iff] using hcap
        exact (not_lt_of_ge (hEq ▸ hT) ht).elim
    exact ⟨sInf A, hT, hA.2⟩
  · rintro ⟨s, hs, hlev⟩
    have hmem : s ∈ A := Or.inl
      ⟨⟨(show (0 : ℝ≥0) ≤ s from zero_le), le_trans hs ht.le⟩, hlev⟩
    exact le_trans (csInf_le hbdd hmem) hs
