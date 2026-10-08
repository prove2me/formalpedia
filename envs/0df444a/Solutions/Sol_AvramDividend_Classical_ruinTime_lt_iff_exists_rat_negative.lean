-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_lt_iff_exists_rat_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:51:42.326713+00:00
-- url     : https://prove2.me/submissions/1aba1f3e-69f3-4610-80eb-b300815c0035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_negative_persists_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a : ℝ≥0∞) :
    ruinTime X x D ω < a ↔
      ∃ q : ℚ, 0 ≤ q ∧
        (Real.toNNReal q : ℝ≥0∞) < a ∧
        riskProcess X x D (Real.toNNReal q) ω < 0 := by
  constructor
  · intro hτ
    unfold ruinTime at hτ
    rw [iInf_lt_iff] at hτ
    rcases hτ with ⟨t, ht⟩
    rw [iInf_lt_iff] at ht
    rcases ht with ⟨hneg, hta⟩
    obtain ⟨δ, hδ, hpersist⟩ :=
      riskProcess_negative_persists_right X x D hD.2.1 ω t hneg
    rcases ENNReal.lt_iff_exists_rat_btwn.mp hta with
      ⟨r, hr0, htr, hra⟩
    let ε : ℝ≥0 := ⟨δ / 2, (half_pos hδ).le⟩
    have hε : 0 < ε := by
      change 0 < δ / 2
      exact half_pos hδ
    have ht_add :
        (t : ℝ≥0∞) < ((t + ε : ℝ≥0) : ℝ≥0∞) := by
      exact ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right t hε)
    have htmin :
        (t : ℝ≥0∞) <
          min (Real.toNNReal r : ℝ≥0∞)
            ((t + ε : ℝ≥0) : ℝ≥0∞) := by
      exact lt_min htr ht_add
    rcases ENNReal.lt_iff_exists_rat_btwn.mp htmin with
      ⟨q, hq0, htq, hqu⟩
    have hqa : (Real.toNNReal q : ℝ≥0∞) < a := by
      have hqr :
          (Real.toNNReal q : ℝ≥0∞) <
            (Real.toNNReal r : ℝ≥0∞) :=
        lt_of_lt_of_le hqu (min_le_left _ _)
      exact lt_trans hqr hra
    have htq_nn : t < Real.toNNReal q :=
      ENNReal.coe_lt_coe.mp htq
    have hq_add_enn :
        (Real.toNNReal q : ℝ≥0∞) <
          ((t + ε : ℝ≥0) : ℝ≥0∞) :=
      lt_of_lt_of_le hqu (min_le_right _ _)
    have hq_add : Real.toNNReal q < t + ε :=
      ENNReal.coe_lt_coe.mp hq_add_enn
    have hdist : dist (Real.toNNReal q) t < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg]
      · have hqreal :
            (Real.toNNReal q : ℝ) < (t : ℝ) + δ / 2 := by
          change (Real.toNNReal q : ℝ) < (t : ℝ) + (ε : ℝ)
          exact_mod_cast hq_add
        linarith
      · exact sub_nonneg.mpr (by
          exact_mod_cast (le_of_lt htq_nn))
    have hqneg :
        riskProcess X x D (Real.toNNReal q) ω < 0 :=
      hpersist (Real.toNNReal q) (le_of_lt htq_nn) hdist
    exact ⟨q, hq0, hqa, hqneg⟩
  · rintro ⟨q, hq0, hqa, hqneg⟩
    unfold ruinTime
    exact lt_of_le_of_lt
      (iInf_le_of_le (Real.toNNReal q)
        (iInf_le_of_le hqneg le_rfl))
      hqa
