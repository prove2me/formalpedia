-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger80_original_allmesh_strict_cash_error_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:32:22.37864+00:00
-- url     : https://prove2.me/submissions/2514ada9-ebd2-44a1-8105-624cc73677ee

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option maxHeartbeats 4000000 in

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∀ m : ℕ, Integrable (E m) P := by
  let δ : ℕ → ℝ := fun m => (n : ℝ) / ((m : ℝ) + 2)
  let F : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  let T : ℕ → Ω → ℝ := fun m ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ ω : ℝ) - δ m) (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  let E : ℕ → Ω → ℝ := fun m ω =>
    (q * δ m * Real.exp (q * (n : ℝ))) * F ω + T m ω
  change ∀ m : ℕ, Integrable (E m) P
  have hρmeas : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable ρ hρstop
  have hρ0 (ω : Ω) : (0 : ℝ) ≤ (ρ ω : ℝ) := by positivity
  have hρT (ω : Ω) : (ρ ω : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hρbound ω
  have hFI : Integrable F P := by
    obtain ⟨_, hStrict, _⟩ :=
      avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
        X x C D hD q (le_of_lt hq) (n : ℝ≥0) (fun _ => ρ)
        (by intro k; exact hρmeas) (by intro k ω; exact hρbound ω)
    exact hStrict 0
  have hTI (m : ℕ) : Integrable (T m) P :=
    avram_p3_grid3_original_random_strict_contact_tail_real_integrable
      X x C D hD q (le_of_lt hq) (n : ℝ≥0)
      (fun ω => (ρ ω : ℝ)) hρmeas hρ0 hρT (δ m)
  intro m
  exact (hFI.const_mul (q * δ m * Real.exp (q * (n : ℝ)))).add (hTI m)
