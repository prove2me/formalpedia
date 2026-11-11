-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger42_original_strict_discounted_cash_mesh_error_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:54:42.961279+00:00
-- url     : https://prove2.me/submissions/6be8347d-c21f-46c9-8563-b41c49c69ce6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_strict_delta_antitone_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original discounted strict cash envelope controls both physical mesh errors. -/
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
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by
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
  change ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
    Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε
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
  have hTI (m : ℕ) : Integrable (T m) P := by
    exact avram_p3_grid3_original_random_strict_contact_tail_real_integrable
      X x C D hD q (le_of_lt hq) (n : ℝ≥0)
      (fun ω => (ρ ω : ℝ)) hρmeas hρ0 hρT (δ m)
  have hEI (m : ℕ) : Integrable (E m) P :=
    (hFI.const_mul (q * δ m * Real.exp (q * (n : ℝ)))).add (hTI m)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨_, _, hδ0⟩ :=
    avram_p3_grid4_uniform_strict_delta_antitone_vanishes (n : ℝ) hnR
  have hTail : Tendsto (fun m => ∫ ω, T m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [T, δ] using
      (avram_gledger40_original_bounded_stop_strict_last_cell_L1_vanish
        X x C D hD q (le_of_lt hq) n hn ρ hρstop hρbound)
  have hFirst : Tendsto
      (fun m => (q * δ m * Real.exp (q * (n : ℝ))) * (∫ ω, F ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto
        (fun _ : ℕ => q * Real.exp (q * (n : ℝ)) * (∫ ω, F ω ∂P))
        atTop (𝓝 (q * Real.exp (q * (n : ℝ)) * (∫ ω, F ω ∂P))) :=
      tendsto_const_nhds
    have ht := hc.mul hδ0
    simpa [mul_assoc, mul_left_comm, mul_comm] using ht
  have hSum : Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    have ht := hFirst.add hTail
    convert ht using 1
    · funext m
      dsimp only [E]
      rw [integral_add (hFI.const_mul _) (hTI m), integral_const_mul]
    · norm_num
  intro ε hε
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    (hSum.eventually (eventually_lt_nhds hε))
  exact ⟨k, fun m hm => ⟨hEI m, le_of_lt (hk m hm)⟩⟩
