-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_topcap_positive_shift_stopped_source_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:04:53.010283+00:00
-- url     : https://prove2.me/submissions/4961ceb5-d175-446d-84cd-994d1907ff33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_topcap_positive_shift_pathwise_intrinsic_budget
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_compact_kernel_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_intrinsic_NX_BV_signed_mean_zero_no_P2
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_strict_reward_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
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
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Fδ : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω + δ)
       else 0)
    Integrable Fδ P ∧ (∫ ω, Fδ ω ∂P) ≤ w (x + δ) := by
  classical
  intro S Fδ
  letI : IsProbabilityMeasure P := X.isProbability
  have hF : Integrable Fδ P := avram_chat24_positive_shift_strict_reward_integrable
    X hBV q hq w C hw_cont hw0 hw_neg hw_smooth hw_grad x D hD T hT hTpos hTop δ hδ
  let a : ℝ := min δ 1 / 2
  let b : ℝ := x + δ + T * X.drift + 1
  have hd : 0 < X.drift :=
    (avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
      X hX hBV).1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a ≤ 2 := by dsimp [a]; linarith [min_le_right δ (1 : ℝ)]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [min_le_left δ (1 : ℝ), mul_nonneg hT (le_of_lt hd)]
  obtain ⟨L, R, hL, hR, hLip, hW⟩ :=
    avram_chat24_positive_shift_compact_kernel_bounds w hw_cont hw_neg
      (hw_smooth.mono fun y hy => ⟨hy, by simp [hTop]⟩) a b ha hab
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  have hτBound (ω : Ω) : τ ω ≤ S := by
    exact ENNReal.toNNReal_mono (by simp) (min_le_right _ (S : ℝ≥0∞))
  have hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) := by
    convert (ruinTime_stopping_rightCont_filtration X x D hD.1.1).min_const S using 1
    funext ω
    exact ENNReal.coe_toNNReal
      (ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top))
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
  let E : Set (ℝ≥0 × Ω) := {p | Y p ∈ Icc a b}
  have hYm : Measurable[𝓕.rightCont.predictable] Y :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X (x + δ) D hD.1.1).measurable
  have hEm : MeasurableSet[𝓕.rightCont.predictable] E :=
    measurableSet_Icc.preimage hYm
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if p.1 ∈ E ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) *
      (w (Y p.1 + p.2) - w (Y p.1)) else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
  obtain ⟨hM, hMzero⟩ : Integrable M P ∧ (∫ ω, M ω ∂P) = 0 :=
    avram_p3_2_original_intrinsic_NX_BV_signed_mean_zero_no_P2
    X hBV NX (fun _ => rfl) S τ hτBound hτ (x + δ) D hD.1.1
    w hw_cont hw_neg q (le_of_lt hq) a b L R ha ha2 hab hL hR hLip hW
    E hEm (fun _ hp => hp) X.ν_integrable G
    (fun p => congrArg (fun d : Decidable (p.1 ∈ E ∧ p.2 < 0) => @ite ℝ _ d _ 0)
      (Subsingleton.elim _ _)) H rfl
  have hp : ∀ᵐ ω ∂P, Fδ ω ≤ w (x + δ) + M ω := by
    have hp := avram_chat24_bv_topcap_positive_shift_pathwise_intrinsic_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos hTop δ hδ
    simpa only [Fδ, M, NX, H, G, E, mem_setOf_eq, ite_and] using hp
  refine ⟨hF, ?_⟩
  calc
    (∫ ω, Fδ ω ∂P) ≤ ∫ ω, w (x + δ) + M ω ∂P :=
      integral_mono_ae hF ((integrable_const _).add hM) hp
    _ = w (x + δ) := by
      rw [integral_add (integrable_const _) hM, hMzero]
      simp
