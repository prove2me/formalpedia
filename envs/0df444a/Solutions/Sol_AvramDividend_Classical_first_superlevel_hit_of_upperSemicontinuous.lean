-- Prove2me | solution 1 for AvramDividend.Classical.first_superlevel_hit_of_upperSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:53:09.413995+00:00
-- url     : https://prove2.me/submissions/989bf668-7590-496f-8f88-6aa89afd2c13

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bornology.Real
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
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hx : 0 < x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ R t) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩ R ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ x ≤ R T ∧
      ∀ s : ℝ≥0, s ≤ ζ → x ≤ R s → T ≤ s := by
  let A : Set ℝ≥0 := Icc 0 ζ ∩ R ⁻¹' Ici x
  have hcomp : IsCompact A :=
    UpperSemicontinuousOn.isCompact_inter_preimage_Ici
      husc isCompact_Icc x
  obtain ⟨t, ht, hxt⟩ := hHit
  have htm : t ∈ A :=
    ⟨⟨(show (0 : ℝ≥0) ≤ t from zero_le), le_of_lt ht⟩, hxt⟩
  have hne : A.Nonempty := ⟨t, htm⟩
  have hmin : sInf A ∈ A := hcomp.sInf_mem hne
  have hvalue : x ≤ R (sInf A) := hmin.2
  have hbelow : BddBelow A :=
    ⟨0, fun s hs => hs.1.1⟩
  have hfirst : ∀ s ∈ A, sInf A ≤ s := by
    intro s hs
    exact csInf_le hbelow hs
  have hpositive : 0 < sInf A := by
    apply pos_iff_ne_zero.mpr
    intro heq
    have hcontradiction : x ≤ (0 : ℝ) := by
      simpa only [heq, hzero] using hvalue
    exact (not_le_of_gt hx) hcontradiction
  have hbefore : sInf A < ζ :=
    lt_of_le_of_lt (hfirst t htm) ht
  refine ⟨sInf A, rfl, hpositive, hbefore, hvalue, ?_⟩
  intro s hs hxs
  exact hfirst s ⟨⟨(show (0 : ℝ≥0) ≤ s from zero_le), hs⟩, hxs⟩
