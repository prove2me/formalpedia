-- Prove2me | solution 2 for AvramDividend.Classical.avram_a19_top_cap_original_full_T_HJB_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:58:51.680649+00:00
-- url     : https://prove2.me/submissions/cb3eca21-93fd-4edc-a342-a6e7ea207b4b

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_topcap_positive_shift_stopped_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by
  classical
  intro S
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  have hF : Integrable F P :=
    (avram_p3_bv_original_strict_reward_L1_nonnegative X hBV x C D hD
      w hw_cont hw_neg q (le_of_lt hq) T hT hTpos hw_nonneg).1
  have hsm : ContDiffOn ℝ 1 w (Ioi 0) := by
    apply hw_smooth.mono
    intro y hy
    exact ⟨hy, by simp [hTop]⟩
  have hmono : MonotoneOn w (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hw_cont
    · simpa only [interior_Ici] using hsm.differentiableOn (by norm_num)
    · intro y hy
      have hypos : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      exact le_trans (by norm_num) (hw_grad y hypos (by simp [hTop]))
  have hbound (δ : ℝ) (hδ : 0 < δ) : (∫ ω, F ω ∂P) ≤ w (x + δ) := by
    obtain ⟨hI, hB⟩ := avram_chat24_bv_topcap_positive_shift_stopped_source_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos hTop δ hδ
    apply le_trans (integral_mono_ae hF hI ?_) hB
    filter_upwards [] with ω
    dsimp [F]
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · dsimp only [S] at hs ⊢
      simp only [hs, if_true, add_le_add_iff_left]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
      have hy : 0 ≤ riskProcess X x D S ω := by
        by_contra hn
        have hr : ruinTime X x D ω ≤ (S : ℝ≥0∞) :=
          iInf_le_of_le S (iInf_le _ (lt_of_not_ge hn))
        exact (not_le_of_gt hs) hr
      exact hmono hy (add_nonneg hy (le_of_lt hδ))
        (le_add_of_nonneg_right (le_of_lt hδ))
    · dsimp only [S] at hs ⊢
      simp only [hs, if_false, add_zero, le_refl]
  have hlimx : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (nhds x) := by
    have hconst : Tendsto (fun _ : ℕ => x) atTop (nhds x) := tendsto_const_nhds
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using hconst.add hinv
  have hlim : Tendsto (fun n : ℕ => w (x + 1 / ((n : ℝ) + 1)))
      atTop (nhds (w x)) := by
    apply Filter.Tendsto.comp (hw_cont x hx)
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlimx, Eventually.of_forall ?_⟩
    intro n
    show 0 ≤ x + 1 / ((n : ℝ) + 1)
    positivity
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hbound _ (by positivity))
