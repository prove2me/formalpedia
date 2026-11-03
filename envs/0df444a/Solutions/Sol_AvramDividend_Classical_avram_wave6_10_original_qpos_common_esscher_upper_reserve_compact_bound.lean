-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_upper_reserve_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:03:52.979963+00:00
-- url     : https://prove2.me/submissions/2de4f21d-4999-4dc4-92be-e695dfbc4c6c

import Mathlib
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
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * R))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * R)) := by
  obtain ⟨θ, hθ, hbound⟩ :=
    avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
      X q hq
  refine ⟨θ, hθ, ?_⟩
  intro R x hx
  obtain ⟨hcap, hunrestricted⟩ := hbound x
  have hexp :
      ENNReal.ofReal (Real.exp (θ * x)) ≤
        ENNReal.ofReal (Real.exp (θ * R)) :=
    ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hx (le_of_lt hθ)))
  constructor
  · intro C
    exact (hcap C).trans hexp
  · exact hunrestricted.trans hexp
