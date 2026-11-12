-- Prove2me | solution 39 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:36:29.844643+00:00
-- url     : https://prove2.me/submissions/18307011-9ccd-41b4-a275-dd23aabc5f45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_drift_discarded_real_to_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_finitecap_centred_cash
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_topcap_centred_cash_finite_activity
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_topcap_centred_cash_infinite_activity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hw_smooth_conj :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    exact ⟨fun hNot => False.elim (hNot hBV), fun _ => hw_smooth⟩
  obtain ⟨hGen, hGrad, hNonneg, hJump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hw_smooth_conj hw_hjb x hxc D hD
  by_cases hT0 : T = 0
  · subst T
    exact admissible_cap_truncated_zero_horizon_hjb_bound
      X q x w C hw_cont hw0 hw_smooth_conj hw_hjb D hD hxc
  · have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hT0 h.symm)
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hTpos⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    have hCases : ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
        (∀ n, 0 < η n) ∧ Tendsto η atTop (nhds (0 : ℝ)) ∧
        (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + M n ω + max (Err n ω) 0) ∧
        (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by
      by_cases hTop : C = ⊤
      · by_cases hActivity : X.ν (Iio (0 : ℝ)) < ⊤
        · exact avram_chat24_bv_topcap_centred_cash_finite_activity
            X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
            hGen hGrad x hx hxc D hD hNonneg hJump T hTpos hTop hActivity
        · exact avram_chat24_bv_topcap_centred_cash_infinite_activity
            X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
            hGen hGrad x hx hxc D hD hNonneg hJump T hTpos hTop hActivity
      · exact avram_chat24_bv_finitecap_centred_cash
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hGen hGrad x hx hxc D hD hNonneg hJump T hTpos hTop
    obtain ⟨M, Err, η, hηpos, hηlim, hM, hErr, hPhysical, hMean⟩ := hCases
    have hErrorLimit :
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) :=
      squeeze_zero (fun n => integral_nonneg (fun ω => le_max_right (Err n ω) 0))
        hMean hηlim
    apply avram_bv_route11_drift_discarded_real_to_closed_cash
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGrad
      x hx hxc D hD hJump T hTpos
    dsimp only
    refine ⟨M, Err, ?_, hErr, hErrorLimit, hPhysical⟩
    intro n
    exact ⟨(hM n).1, le_of_eq (hM n).2⟩
