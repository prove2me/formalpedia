-- Prove2me | solution 1 for AvramDividend.Classical.finite_excursion_height_attained_of_upperSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:50:25.811778+00:00
-- url     : https://prove2.me/submissions/8ccd1e96-32a2-41e4-9c65-6aec41c23d81

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hEnd : R ζ = 0)
    (x : ℝ) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → R t ≤ x)
    (hSharp : ∀ y : ℝ, y < x →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < R t) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧ R T = x := by
  have hne : (Icc (0 : ℝ≥0) ζ).Nonempty :=
    ⟨0, ⟨le_refl _, le_of_lt hζ⟩⟩
  obtain ⟨T, hT, hMax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn hne isCompact_Icc husc
  have hupper : R T ≤ x := hBound T hT.2
  have hlower : x ≤ R T := by
    by_contra hnot
    have hless : R T < x := lt_of_not_ge hnot
    obtain ⟨t, ht, hgreater⟩ := hSharp (R T) hless
    have hle : R t ≤ R T := hMax ⟨(show (0 : ℝ≥0) ≤ t from zero_le), ht⟩
    exact (not_lt_of_ge hle) hgreater
  have heq : R T = x := le_antisymm hupper hlower
  have hTpos : 0 < T := by
    rcases (show (0 : ℝ≥0) ≤ T from zero_le).eq_or_lt with he | hpos
    · have hxzero : (0 : ℝ) = x := by
        calc
          (0 : ℝ) = R (0 : ℝ≥0) := hzero.symm
          _ = R T := congrArg R he
          _ = x := heq
      exact False.elim ((ne_of_lt hx) hxzero)
    · exact hpos
  have hTlt : T < ζ := by
    rcases hT.2.eq_or_lt with he | hlt
    · have hxzero : (0 : ℝ) = x := by
        calc
          (0 : ℝ) = R ζ := hEnd.symm
          _ = R T := congrArg R he.symm
          _ = x := heq
      exact False.elim ((ne_of_lt hx) hxzero)
    · exact hlt
  exact ⟨T, hTpos, hTlt, heq⟩
