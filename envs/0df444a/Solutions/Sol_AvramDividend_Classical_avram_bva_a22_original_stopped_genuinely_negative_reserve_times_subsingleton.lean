-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:05:54.62401+00:00
-- url     : https://prove2.me/submissions/399b2bdc-7617-4da8-bb4a-9534660419b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Set.Subsingleton {t : ℝ≥0 |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        riskProcess X x D t ω < 0} := by
  intro a ha b hb
  have ha_le : ruinTime X x D ω ≤ (a : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le a (iInf_le_of_le ha.2.2 le_rfl)
  have hb_le : ruinTime X x D ω ≤ (b : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le b (iInf_le_of_le hb.2.2 le_rfl)
  have ha_eq : (a : ℝ≥0∞) = ruinTime X x D ω :=
    le_antisymm ha.2.1 ha_le
  have hb_eq : (b : ℝ≥0∞) = ruinTime X x D ω :=
    le_antisymm hb.2.1 hb_le
  exact_mod_cast ha_eq.trans hb_eq.symm
