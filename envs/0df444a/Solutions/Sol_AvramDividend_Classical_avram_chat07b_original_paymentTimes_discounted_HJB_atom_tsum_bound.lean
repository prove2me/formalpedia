-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_paymentTimes_discounted_HJB_atom_tsum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:30:53.688201+00:00
-- url     : https://prove2.me/submissions/bde953d6-1201-4d32-acdd-ba947bcbd946

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The literal original stopped paymentTimes set automatically supplies the
strict-pre-ruin-or-zero guard for the full discounted HJB atom sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ) :
    let S : Set ℝ≥0 :=
      (fun s : ℝ => s.toNNReal) '' (paymentTimes (ruinTime X x D ω) ∩ Iic T)
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        dividendMeasure D ω {(t.1 : ℝ)}) ≤
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        ENNReal.ofReal
          (w (riskProcess X x D t.1 ω) -
            w (riskProcess X x D t.1 ω -
              (rightLimit D t.1 ω - D t.1 ω)))) := by
  have hActive : ∀ t ∈
      ((fun s : ℝ => s.toNNReal) ''
        (paymentTimes (ruinTime X x D ω) ∩ Iic T)),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
    intro t ht
    rcases ht with ⟨s, hs, rfl⟩
    exact (paymentTimes_membership_to_nNReal_active
      (ruinTime X x D ω) s hs.1).2
  exact avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
    X x D hD w q hjump ω _ hActive
