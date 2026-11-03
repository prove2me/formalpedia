-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:38:11.187453+00:00
-- url     : https://prove2.me/submissions/8715ef67-4359-4ded-98d4-1c716cff195f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by
  have hθpos : 0 < ENNReal.ofReal θ := ENNReal.ofReal_pos.mpr hθ
  have hθne : ENNReal.ofReal θ ≠ 0 := ne_of_gt hθpos
  have hrhsne :
      ENNReal.ofReal (Real.exp (θ * x)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfinite (v : ℝ≥0∞)
      (hv : ENNReal.ofReal θ * v ≤
        ENNReal.ofReal (Real.exp (θ * x))) : v < ⊤ := by
    by_contra hnot
    have hvtop : v = ⊤ := le_antisymm le_top (not_lt.mp hnot)
    have hm : ENNReal.ofReal θ * v = ⊤ := by
      simp [hvtop, hθne]
    rw [hm] at hv
    exact hrhsne (le_antisymm le_top hv)
  obtain ⟨hcap, hfull⟩ :=
    avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
      X x θ hθ q hq
  exact ⟨fun C => hfinite _ (hcap C), hfinite _ hfull⟩
