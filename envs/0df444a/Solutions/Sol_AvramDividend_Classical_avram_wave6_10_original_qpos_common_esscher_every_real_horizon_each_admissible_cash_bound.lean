-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:39.235629+00:00
-- url     : https://prove2.me/submissions/91ecac80-289f-4e94-977e-e9be1899efc3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One common Esscher parameter bounds every actual admissible truncated Stieltjes
    payment, for every real horizon and every initial reserve below R. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D → ∀ T : ℝ,
          ENNReal.ofReal θ *
            (∫⁻ ω, ∫⁻ t in
              paymentTimes (ruinTime X x D ω) ∩ Iic T,
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (Real.exp (θ * R)) := by
  obtain ⟨θ, hθ, hfull⟩ :=
    avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound
      X q hq
  refine ⟨θ, hθ, ?_⟩
  intro R x hx C D hD T
  have htrunc :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by
    unfold dividendValue
    apply MeasureTheory.lintegral_mono
    intro ω
    apply MeasureTheory.lintegral_mono_set
    exact Set.inter_subset_left
  calc
    ENNReal.ofReal θ *
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal θ * dividendValue X q x D :=
      mul_le_mul_of_nonneg_left htrunc bot_le
    _ ≤ ENNReal.ofReal (Real.exp (θ * R)) :=
      hfull R x hx C D hD
