-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_jump_times_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:52:40.733291+00:00
-- url     : https://prove2.me/submissions/22f9201b-fd41-4d98-a6d7-8c99f7e50781

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_countable_positive_rightLimit_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Set.Countable {t : ℝ≥0 | 0 < t ∧
      x + X.X t ω - rightLimit D t ω ≠
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by
  have hDcount : Set.Countable
      {t : ℝ≥0 | rightLimit D t ω ≠ D t ω} := by
    have hpre :
        ((fun t : ℝ≥0 => (t : ℝ)) ⁻¹'
          {r : ℝ | 0 ≤ r ∧
            rightLimit D r.toNNReal ω ≠ D r.toNNReal ω}).Countable :=
      (dividendStrategy_countable_positive_rightLimit_jumps D hD ω).preimage
        NNReal.coe_injective
    simpa [Set.preimage, Real.toNNReal_coe] using hpre
  have hXcount :=
    avram_wave4_p2_all_original_levy_jump_times_countable X ω
  apply (hXcount.union hDcount).mono
  intro t ht
  by_cases hX : X.X t ω =
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  · right
    intro hzeroD
    apply ht.2
    rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD ω t ht.1, hX, hzeroD]
  · left
    exact ⟨ht.1, hX⟩