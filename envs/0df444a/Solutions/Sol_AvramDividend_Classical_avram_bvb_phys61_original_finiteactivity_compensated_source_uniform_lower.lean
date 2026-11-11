-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys61_original_finiteactivity_compensated_source_uniform_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:54:37.042196+00:00
-- url     : https://prove2.me/submissions/7f1f92be-db35-4d60-9093-771489135a2a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys54_supported_integral_norm_le_count
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
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
    let M : ℕ → Ω → ℝ := fun n ω =>
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    ∃ K : Ω → ℝ, Integrable K P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, -K ω ≤ M n ω := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ U H NX M
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hν : ν Set.univ < ⊤ := by
    simpa [ν] using hActivity
  let ηReal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 T)
  have hηReal : ηReal Set.univ < ⊤ := by
    simpa [ηReal] using (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))
  letI : IsFiniteMeasure ηReal := ⟨hηReal⟩
  let η : Measure ℝ≥0 := ηReal.map Real.toNNReal
  letI : IsFiniteMeasure η := Measure.isFiniteMeasure_map ηReal Real.toNNReal
  have hη : η Set.univ < ⊤ := measure_lt_top η Set.univ
  obtain ⟨W, hW0, hW⟩ :=
    avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
      q hq w C hFinite hw_cont hw_neg
  have hH (n : ℕ) (ω : Ω) (t : ℝ≥0) (z : ℝ) :
      ‖H n ((t, ω), z)‖ ≤ W := by
    dsimp [H]
    split_ifs with hm
    · rcases hm with ⟨_, _, _, hu0, huC, hz⟩
      simpa only [Real.norm_eq_abs] using
        hW (t : ℝ) (U t ω) z t.property hu0 huC hz
    · simpa using hW0
  let J : ℕ → Ω → ℝ := fun n ω =>
    ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
  let V : ℕ → Ω → ℝ := fun n ω =>
    ∫ t, ∫ z, H n ((t, ω), z) ∂ν ∂η
  let N : Ω → ℝ := fun ω =>
    ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
  obtain ⟨KJ, hKJ0, hNI, hJ⟩ :=
    avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
      X hBV q hq w C hC hFinite hw_cont hw_neg
      x D hD T hT hActivity
  have hInner (n : ℕ) (ω : Ω) (t : ℝ≥0) :
      ‖∫ z, H n ((t, ω), z) ∂ν‖ ≤ W * (ν Set.univ).toReal := by
    by_cases hf : Integrable (fun z => H n ((t, ω), z)) ν
    · exact avram_bvb_phys54_supported_integral_norm_le_count
        ν Set.univ MeasurableSet.univ hν
        (fun z => H n ((t, ω), z)) hf
        (by simp) W hW0 (by intro z hz; exact hH n ω t z)
    · simp [integral_undef hf, mul_nonneg hW0 ENNReal.toReal_nonneg]
  have hVbound (n : ℕ) (ω : Ω) :
      ‖V n ω‖ ≤ (W * (ν Set.univ).toReal) * (η Set.univ).toReal := by
    by_cases hf : Integrable
        (fun t => ∫ z, H n ((t, ω), z) ∂ν) η
    · dsimp [V]
      exact avram_bvb_phys54_supported_integral_norm_le_count
        η Set.univ MeasurableSet.univ hη
        (fun t => ∫ z, H n ((t, ω), z) ∂ν) hf
        (by simp) (W * (ν Set.univ).toReal)
        (mul_nonneg hW0 ENNReal.toReal_nonneg)
        (by intro t ht; exact hInner n ω t)
    · dsimp [V]
      simp [integral_undef hf, mul_nonneg
        (mul_nonneg hW0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg]
  let K : Ω → ℝ := fun ω =>
    KJ * N ω + (W * (ν Set.univ).toReal) * (η Set.univ).toReal
  have hKI : Integrable K P := by
    dsimp [K]
    exact (hNI.const_mul KJ).add (integrable_const _)
  refine ⟨K, hKI, ?_⟩
  intro n
  filter_upwards [hJ n] with ω hj
  have hJlower : -(KJ * N ω) ≤ J n ω := by
    have hh := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hj)).1
    linarith
  have hVupper : V n ω ≤
      (W * (ν Set.univ).toReal) * (η Set.univ).toReal :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hVbound n ω)
  change -K ω ≤ J n ω - V n ω
  dsimp [K]
  linarith
