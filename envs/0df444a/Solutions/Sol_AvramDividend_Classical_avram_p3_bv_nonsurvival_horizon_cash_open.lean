-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_nonsurvival_horizon_cash_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:38:50.00122+00:00
-- url     : https://prove2.me/submissions/387a90bf-7b92-4856-9902-695d65bcab41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a positive horizon outside strict survival, the original stopped
    dividend measure pays no right-jump atom at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P, ¬ ((S : ℝ≥0∞) < ruinTime X x D ω) →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hsplit := avram_p3_bv_real_cash_split_ae X x C D hD q T hT
  filter_upwards [hsplit] with ω hω
  intro hnosurvive
  have hSval : (S : ℝ) = T := rfl
  have hSenn : ENNReal.ofReal T = (S : ℝ≥0∞) := by
    rw [← hSval]
    exact ENNReal.ofReal_coe_nnreal
  have hnotPaid : T ∉ paymentTimes (ruinTime X x D ω) := by
    intro ht
    change 0 ≤ T ∧ (T = 0 ∨ ENNReal.ofReal T < ruinTime X x D ω) at ht
    rcases ht.2 with hzero | hbefore
    · exact (ne_of_gt hTpos) hzero
    · exact hnosurvive (by rw [← hSenn]; exact hbefore)
  have hAtomEmpty : paymentTimes (ruinTime X x D ω) ∩
      ({T} : Set ℝ) = ∅ := by
    ext t
    constructor
    · rintro ⟨hp, heq⟩
      simp only [Set.mem_singleton_iff] at heq
      exact False.elim (hnotPaid (heq ▸ hp))
    · intro h
      simp at h
  simpa [hAtomEmpty] using hω
