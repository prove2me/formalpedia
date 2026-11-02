-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:03:17.711198+00:00
-- url     : https://prove2.me/submissions/eec9870d-7505-4038-8e51-d08be0e44866

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform in every original time and sample, the signed nonlinear stopped
generator drift on discarded negative Lévy source marks has a deterministic
vanishing bound, from the actual source Lévy quadratic integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
        ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ≤ err n := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
    ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
      ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ≤ err n
  obtain ⟨M, hM, hglobal⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  let S (n : ℕ) : ℝ≥0∞ := ∫⁻ z in B n, f z ∂X.ν
  let err (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal M * S n
  have hfmeas : Measurable f := by fun_prop
  have hfint : (∫⁻ z, f z ∂X.ν) ≠ ⊤ := ne_of_lt X.ν_integrable
  have hSzero : (⨅ n : ℕ, S n) = 0 :=
    avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
      X.ν f hfmeas hfint B hBm hBanti hBempty
  have hSanti : Antitone S := by
    intro i j hij
    exact lintegral_mono_set (hBanti hij)
  have herrAnti : Antitone err := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (hSanti hij) bot_le
  have herrInf : (⨅ n : ℕ, err n) = 0 := by
    by_cases hc : ENNReal.ofReal M = 0
    · simp [err, hc]
    · change (⨅ n : ℕ, ENNReal.ofReal M * S n) = 0
      rw [← ENNReal.mul_iInf_of_ne hc
        (ne_of_lt ENNReal.ofReal_lt_top)]
      simp [hSzero]
  have herrConv : Tendsto err atTop (𝓝 0) := by
    have ht := tendsto_atTop_iInf herrAnti
    rw [herrInf] at ht
    exact ht
  refine ⟨err, herrConv, ?_⟩
  intro n p
  have heq :
      (∫ z in B n, HS (p,z) ∂X.ν) =
      (∫ z in B n, JG (p,z) ∂X.ν) := by
    simpa [HS, H, JG, Y] using
      (avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
        X x D hD w u v δ p (B n) (hBm n) (hBneg n))
  have hpoint (z : ℝ) (hz : z ∈ B n) :
      ENNReal.ofReal (|HS (p,z)|) ≤ ENNReal.ofReal M * f z := by
    rw [← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_ofReal (hglobal p z (hBneg n hz))
  have hbound :
      (∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤ err n := by
    calc
      (∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤
          ∫⁻ z in B n, ENNReal.ofReal M * f z ∂X.ν := by
        apply setLIntegral_mono (by fun_prop)
        intro z hz
        exact hpoint z hz
      _ = err n := by
        change (∫⁻ z in B n, ENNReal.ofReal M * f z ∂X.ν) =
          ENNReal.ofReal M * S n
        rw [lintegral_const_mul _ hfmeas]
  calc
    ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ =
        ‖∫ z in B n, HS (p,z) ∂X.ν‖ₑ :=
      congrArg (fun r : ℝ => ‖r‖ₑ) heq.symm
    _ ≤ ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν := by
      simpa only [Real.enorm_eq_ofReal_abs] using
        (enorm_integral_le_lintegral_enorm
          (μ := X.ν.restrict (B n)) (fun z : ℝ => HS (p,z)))
    _ ≤ err n := hbound
