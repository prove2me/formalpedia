-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_barrier_eq_control_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:16:56.689057+00:00
-- url     : https://prove2.me/submissions/b679c994-f1f5-4602-a91b-8ef65ec6c7cb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    barrierStrategy X 0 0 t ω = D t ω := by
  have hz : D 0 ω = 0 := hD.1.1.1 ω
  have hm : Monotone (fun s => D s ω) := hD.1.1.2.1 ω
  have h0t : (0 : ℝ≥0) ≤ t := bot_le
  have hpos : 0 ≤ D t ω := by
    simpa [hz] using hm h0t
  have heq (s : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
      D s ω = X.X s ω := by
    have hsr : (s : ℝ≥0∞) < ruinTime X 0 D ω :=
      lt_of_le_of_lt (by exact_mod_cast hst) ht
    have hn : 0 ≤ riskProcess X 0 D s ω := by
      by_contra hh
      have hsneg : riskProcess X 0 D s ω < 0 := lt_of_not_ge hh
      have hle : ruinTime X 0 D ω ≤ (s : ℝ≥0∞) := by
        unfold ruinTime
        exact iInf_le_of_le s (iInf_le _ hsneg)
      exact (not_lt_of_ge hle) hsr
    have hc : ENNReal.ofReal (riskProcess X 0 D s ω) ≤ 0 :=
      hD.2 ω s hs
    have hc0 : ENNReal.ofReal (riskProcess X 0 D s ω) = 0 :=
      le_antisymm hc bot_le
    have hn0 : riskProcess X 0 D s ω ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hc0
    have hv : riskProcess X 0 D s ω = 0 := le_antisymm hn0 hn
    dsimp [riskProcess] at hv
    linarith
  let st : Icc (0 : ℝ≥0) t := ⟨t, ⟨h0t, le_rfl⟩⟩
  letI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨st⟩
  have hpoint (s : Icc (0 : ℝ≥0) t) : X.X s ω ≤ D t ω := by
    by_cases hs0 : (s : ℝ≥0) = 0
    · simpa [hs0, X.X_zero ω] using hpos
    · have hs : 0 < (s : ℝ≥0) :=
        pos_iff_ne_zero.mpr hs0
      rw [← heq s hs s.property.2]
      exact hm s.property.2
  have hbd : BddAbove (Set.range (fun s : Icc (0 : ℝ≥0) t => X.X s ω)) := by
    refine ⟨D t ω, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hpoint s
  have hsup_le :
      (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤ D t ω :=
    ciSup_le hpoint
  have hsup_ge :
      D t ω ≤ (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) := by
    rw [heq t ht0 le_rfl]
    exact le_ciSup hbd st
  have hsup_eq :
      (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) = D t ω :=
    le_antisymm hsup_le hsup_ge
  simp [barrierStrategy, ht0.ne', hsup_eq, hpos]
