-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:15:55.032273+00:00
-- url     : https://prove2.me/submissions/7eac2b1c-1040-42fc-b7e5-bff1640d8076

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D →
          ENNReal.ofReal θ * dividendValue X q x D ≤
            ENNReal.ofReal (Real.exp (θ * R)) := by
  obtain ⟨θ, hθ, hbound⟩ :=
    avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
      X q hq
  refine ⟨θ, hθ, ?_⟩
  intro R x hx C D hD
  have hstrategy :
      dividendValue X q x D ≤ valueFunctionLe X q C x := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hexp :
      ENNReal.ofReal (Real.exp (θ * x)) ≤
        ENNReal.ofReal (Real.exp (θ * R)) :=
    ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hx (le_of_lt hθ)))
  calc
    ENNReal.ofReal θ * dividendValue X q x D ≤
        ENNReal.ofReal θ * valueFunctionLe X q C x :=
      mul_le_mul_of_nonneg_left hstrategy bot_le
    _ ≤ ENNReal.ofReal (Real.exp (θ * x)) := (hbound x).1 C
    _ ≤ ENNReal.ofReal (Real.exp (θ * R)) := hexp
