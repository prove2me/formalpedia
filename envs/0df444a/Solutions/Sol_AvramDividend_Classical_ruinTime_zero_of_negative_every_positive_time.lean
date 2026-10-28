-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_zero_of_negative_every_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:27:11.947823+00:00
-- url     : https://prove2.me/submissions/ff6728ba-569d-4f83-a4c5-92401ceabcbd

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strictly negative reserves arbitrarily close to zero force immediate ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hneg : ∀ t : ℝ≥0, 0 < t → riskProcess X x D t ω < 0) :
    ruinTime X x D ω = 0 := by
  have hle (t : ℝ≥0) (ht : 0 < t) :
      ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
    change (⨅ s : ℝ≥0,
        ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) ≤
      (t : ℝ≥0∞)
    calc
      _ ≤ (⨅ _h : riskProcess X x D t ω < 0, (t : ℝ≥0∞)) :=
        iInf_le (fun s : ℝ≥0 =>
          ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) t
      _ ≤ (t : ℝ≥0∞) :=
        iInf_le (fun _h : riskProcess X x D t ω < 0 =>
          (t : ℝ≥0∞)) (hneg t ht)
  rcases eq_or_lt_of_le (bot_le :
      (0 : ℝ≥0∞) ≤ ruinTime X x D ω) with hz | hp
  · exact hz.symm
  · obtain ⟨t, ht0, htτ⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp hp
    have htp : (0 : ℝ≥0) < t := ENNReal.coe_pos.mp ht0
    exact False.elim ((not_lt_of_ge (hle t htp)) htτ)
