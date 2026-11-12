-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_shift_strict_reward_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:22:44.744519+00:00
-- url     : https://prove2.me/submissions/55b85606-c490-42c5-a7d3-117f875af67a

import Mathlib
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
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Fδ : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω + δ)
       else 0)
    Integrable Fδ P := by
  classical
  intro S Fδ
  have hsm : ContDiffOn ℝ 1 w (Ioi 0) :=
    hw_smooth.mono fun y hy => ⟨hy, by simp [hTop]⟩
  have hmono : MonotoneOn w (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hw_cont
    · simpa only [interior_Ici] using hsm.differentiableOn (by norm_num)
    · intro y hy
      have hypos : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      exact le_trans (by norm_num) (hw_grad y hypos (by simp [hTop]))
  let v : ℝ → ℝ := fun y => if y < 0 then 0 else w (y + δ)
  have hvcont : ContinuousOn v (Ici 0) := by
    have hc : ContinuousOn (fun y : ℝ => w (y + δ)) (Ici 0) :=
      hw_cont.comp (continuous_id.add continuous_const).continuousOn
        (fun y hy => add_nonneg hy (le_of_lt hδ))
    apply hc.congr
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy
    simp [v, not_lt_of_ge hy0]
  have hvneg : ∀ y < 0, v y = 0 := fun y hy => by simp [v, hy]
  have hvnonneg (y : ℝ) : 0 ≤ v y := by
    by_cases hy : y < 0
    · simp [v, hy]
    · have hyδ : 0 ≤ y + δ := add_nonneg (le_of_not_gt hy) (le_of_lt hδ)
      simpa only [v, hy, if_false] using le_trans hw0 (hmono (by simp) hyδ hyδ)
  have hI := (avram_p3_bv_original_strict_reward_L1_nonnegative
    X hBV x C D hD v hvcont hvneg q (le_of_lt hq) T hT hTpos
    (fun ω t ht hs => hvnonneg (riskProcess X x D t ω))).1
  apply hI.congr
  filter_upwards [] with ω
  dsimp only [Fδ]
  by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hy : ¬ riskProcess X x D S ω < 0 := by
      intro hn
      exact (not_le_of_gt hs) (iInf_le_of_le S (iInf_le _ hn))
    dsimp only [S] at hs hy ⊢
    simp only [hs, if_true, v, hy, if_false]
  · dsimp only [S] at hs ⊢
    simp only [hs, if_false, add_zero]
