-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_fullmask_reward_aefibre_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:16:37.974114+00:00
-- url     : https://prove2.me/submissions/ff1929b6-bd79-44b0-9b31-bbdf427e5e55

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_supported_bounded_finite_measure_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    ∀ n, ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) (NX ω) := by
  intro δ U H NX J
  let S : Set (ℝ≥0 × ℝ) :=
    Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ)
  have hSm : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Iio
  have hPred :=
    AvramDividend.Classical.avram_bvb_topcap_original_marked_predictable
      X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD T hT hActivity
  have hPredLe : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le (⊥ : ℝ≥0)) A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod hA'
    · intro i A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le i) A hA
      exact (measurableSet_Ioi : MeasurableSet (Ioi i)).prod hA'
  have hProdLe : (@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) ≤
      (inferInstance : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)) :=
    by
      change (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ) ≤
        (inferInstance : MeasurableSpace (ℝ≥0 × Ω)).prod
          (inferInstance : MeasurableSpace ℝ)
      unfold MeasurableSpace.prod
      exact sup_le_sup (MeasurableSpace.comap_mono hPredLe) le_rfl

  obtain ⟨K, hK, hReward⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
      X hBV q hq w hw_cont hw_neg x D hD.1.1 (Real.toNNReal T)
  have hCount : ∀ᵐ ω ∂P, (NX ω) S ≠ ⊤ := by
    simpa only [NX, S] using
      (AvramDividend.Classical.avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
        X (ne_of_lt hActivity) (Real.toNNReal T))
  intro n
  filter_upwards [hCount, hReward] with ω hω hRewardω
  let f : ℝ≥0 × ℝ → ℝ := fun p => H n ((p.1, ω), p.2)
  have hReorder : Measurable (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by fun_prop
  have hf : Measurable f := (hPred n).mono hProdLe le_rfl |>.comp hReorder
  have hδ : 0 ≤ δ n := div_nonneg hT.le (by positivity)
  have hSupport : ∀ p : ℝ≥0 × ℝ, p ∉ S → f p = 0 := by
    intro p hp
    by_cases hmask :
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U p.1 ω ∧ ENNReal.ofReal (U p.1 ω) ≤ C ∧ p.2 < 0
    · exfalso
      apply hp
      rcases hmask with ⟨hp0, hpT, hpR, hpU, hpC, hpz⟩
      have hTbound : (p.1 : ℝ) ≤ T :=
        le_of_lt (lt_of_lt_of_le hpT (sub_le_self T hδ))
      have hpnn : p.1 ≤ Real.toNNReal T := by
        have hReal : (p.1 : ℝ) ≤ (Real.toNNReal T : ℝ) := by
          simpa only [Real.coe_toNNReal T hT.le] using hTbound
        exact_mod_cast hReal
      exact ⟨⟨hp0, hpnn⟩, hpz⟩
    · simp only [f, H, if_neg hmask]

  have hBound : ∀ p ∈ S, |f p| ≤ K := by
    intro p hp
    by_cases hmask :
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U p.1 ω ∧ ENNReal.ofReal (U p.1 ω) ≤ C ∧ p.2 < 0
    · have hpoint := hRewardω p.1 hp.1.2
        hmask.2.2.2.1 p.2 hmask.2.2.2.2.2
      simpa only [f, H, U, if_pos hmask] using hpoint
    · simpa only [f, H, if_neg hmask, abs_zero] using hK
  have hFin : (NX ω) S < ⊤ := lt_top_iff_ne_top.mpr hω
  exact AvramDividend.Classical.avram_bvb_topcap_supported_bounded_finite_measure_integrable
    (NX ω) S hSm hFin f hf hSupport K hK hBound
