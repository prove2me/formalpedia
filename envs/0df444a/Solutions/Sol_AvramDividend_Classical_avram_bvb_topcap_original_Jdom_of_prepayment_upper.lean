-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_Jdom_of_prepayment_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:24:43.440971+00:00
-- url     : https://prove2.me/submissions/1454ea7d-1ca7-4e10-8261-6b55b774bc07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys54_supported_integral_norm_le_count
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys51_original_actual_negative_count_L1
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
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hUpper : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ) ≤ T →
      Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤
        x + max (T * X.drift) 0) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω => ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let N : Ω → ℝ := fun ω => ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
    ∃ K : ℝ, 0 ≤ K ∧ Integrable N P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ K * N ω := by
  intro δ U H NX J N
  letI : IsProbabilityMeasure P := X.isProbability
  let S : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ)
  have hSm : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Iio
  let B : ℝ := max 0 (x + max (T * X.drift) 0)
  have hB : 0 ≤ B := le_max_left _ _
  obtain ⟨K, hK, hReward⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound w hw_cont hw_neg B q hB hq
  have hNI : Integrable N P := by
    simpa only [N, NX] using
      (AvramDividend.Classical.avram_bvb_phys51_original_actual_negative_count_L1
        X hBV (Real.toNNReal T) hActivity)
  refine ⟨K, hK, hNI, ?_⟩
  let Nenn : Ω → ℝ≥0∞ := fun ω => (NX ω) S
  have hcount : ∀ᵐ ω ∂P, Nenn ω ≠ ⊤ := by
    simpa only [Nenn, NX, S] using
      (AvramDividend.Classical.avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
        X (ne_of_lt hActivity) (Real.toNNReal T))
  intro n
  filter_upwards [hcount, hUpper] with ω hω hW
  have hSfinite : (NX ω) S < ⊤ := lt_top_iff_ne_top.mpr hω
  let f : ℝ≥0 × ℝ → ℝ := fun p => H n ((p.1, ω), p.2)
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
  have hBound : ∀ p : ℝ≥0 × ℝ, p ∈ S → ‖f p‖ ≤ K := by
    intro p hp
    by_cases hmask :
        0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U p.1 ω ∧ ENNReal.ofReal (U p.1 ω) ≤ C ∧ p.2 < 0
    · rcases hmask with ⟨hp0, hpT, hpR, hpU, hpC, hpz⟩
      have hmask' :
          0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
          (p.1 : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U p.1 ω ∧ ENNReal.ofReal (U p.1 ω) ≤ C ∧ p.2 < 0 :=
        ⟨hp0, hpT, hpR, hpU, hpC, hpz⟩
      have hδbound : (p.1 : ℝ) ≤ T :=
        le_of_lt (lt_of_lt_of_le hpT (sub_le_self T hδ))
      have hUb : U p.1 ω ≤ B := by
        exact (hW p.1 hp0 hδbound).trans (le_max_right _ _)
      have hpoint :=
        hReward (p.1 : ℝ) (U p.1 ω) p.2
          (NNReal.coe_nonneg _) hpU hUb hpz
      simpa only [f, H, if_pos hmask', Real.norm_eq_abs] using hpoint
    · simp only [f, H, if_neg hmask, norm_zero]
      exact hK
  by_cases hf : Integrable f (NX ω)
  · have hMain :=
      avram_bvb_phys54_supported_integral_norm_le_count
        (NX ω) S hSm hSfinite f hf hSupport K hK hBound
    simpa only [f, J, N, Nenn, S] using hMain
  · have hZero : (∫ p, f p ∂(NX ω)) = 0 := integral_undef hf
    change ‖∫ p, f p ∂(NX ω)‖ ≤ K * ((NX ω) S).toReal
    rw [hZero, norm_zero]
    exact mul_nonneg hK ENNReal.toReal_nonneg
