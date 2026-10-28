-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_excursion_first_exact_height_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:33:10.622648+00:00
-- url     : https://prove2.me/submissions/cbd827f9-4353-4799-8526-ac43f8b39cf5

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_positive_height_sSup_attained
import Theorems.Thm_AvramDividend_Classical_first_exact_level_hit_of_upperSemicontinuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) = x) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ reflectedSup X T ω = x ∧
      ∀ s : ℝ≥0, s ≤ ζ → reflectedSup X s ω = x → T ≤ s := by
  let R : ℝ≥0 → ℝ := fun t => reflectedSup X t ω
  have husc : UpperSemicontinuousOn R (Icc 0 ζ) :=
    reflectedSup_upperSemicontinuousOn_Icc X ω ζ
  have hbdd : BddAbove (R '' Icc (0 : ℝ≥0) ζ) :=
    UpperSemicontinuousOn.bddAbove_of_isCompact isCompact_Icc husc
  have hHeightR : sSup (R '' Icc (0 : ℝ≥0) ζ) = x := hHeight
  have hPosSup : 0 < sSup (R '' Icc (0 : ℝ≥0) ζ) := by
    rw [hHeightR]
    exact hx
  obtain ⟨t, _, ht, htHeight⟩ :=
    reflectedSup_positive_height_sSup_attained X ω ζ hζ hEnd hPosSup
  have hBound : ∀ s : ℝ≥0, s ≤ ζ → R s ≤ x := by
    intro s hs
    have hle : R s ≤ sSup (R '' Icc (0 : ℝ≥0) ζ) :=
      le_csSup hbdd ⟨s, ⟨(show (0 : ℝ≥0) ≤ s from zero_le), hs⟩, rfl⟩
    exact hHeightR ▸ hle
  have hVisit : ∃ s : ℝ≥0, s < ζ ∧ x ≤ R s := by
    refine ⟨t, ht, ?_⟩
    exact le_of_eq ((htHeight.trans hHeightR).symm)
  exact first_exact_level_hit_of_upperSemicontinuous
    R ζ x husc (reflectedSup_origin_eq_zero X ω)
    hx hBound hVisit
