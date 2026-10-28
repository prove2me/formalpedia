-- Prove2me | solution 1 for AvramDividend.Classical.usc_compact_sup_level_hit_before_lower_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:43:12.003276+00:00
-- url     : https://prove2.me/submissions/895f31d0-5a2a-4caa-87ea-364fae47a659

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (H : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 H))
    (hSup : sSup (R '' Icc 0 H) = x)
    (hEnd : R H < x) :
    ∃ t : ℝ≥0, t < H ∧ R t = x := by
  obtain ⟨t, ht, hmax⟩ := husc.exists_isMaxOn ⟨0, left_mem_Icc.2 ((zero_le : (0:ℝ≥0) ≤ H))⟩ isCompact_Icc
  have hbdd : BddAbove (R '' Icc 0 H) := ⟨R t, by rintro _ ⟨s, hs, rfl⟩; exact hmax hs⟩
  have h1 : sSup (R '' Icc 0 H) ≤ R t := csSup_le ⟨R 0, 0, left_mem_Icc.2 ((zero_le : (0:ℝ≥0) ≤ H)), rfl⟩
    (by rintro _ ⟨s, hs, rfl⟩; exact hmax hs)
  have h2 : R t ≤ sSup (R '' Icc 0 H) := le_csSup hbdd ⟨t, ht, rfl⟩
  have hx : R t = x := by rw [← hSup]; exact le_antisymm h2 h1
  refine ⟨t, lt_of_le_of_ne ht.2 ?_, hx⟩
  rintro rfl; linarith
