-- Prove2me | solution 1 for AvramDividend.Classical.avram_a37_original_random_fullcell_gaussian_polynomial_residual_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:31:37.630094+00:00
-- url     : https://prove2.me/submissions/b4107961-a56a-4e53-b9a9-93de4eda3c7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_agentC_original_random_fullcell_centred_AE_limit_public
import Theorems.Thm_AvramDividend_Classical_avram_agentC_original_random_fullcell_centred_L2_envelope_public
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ + Δ ≤ (n : ℝ≥0))
    (Z : ℕ → Ω → ℝ)
    (hZeq : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      Z m ω = X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)
    (K : ℝ) (hK : 0 ≤ K) (H : ℕ → Ω → ℝ)
    (hError : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      |H m ω| ≤ K * (|Z m ω| + (Z m ω)^2 + (Δ : ℝ)))
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => |H m ω|) P) :
    Tendsto (fun m => ∫ ω, |H m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hZlim :=
    avram_agentC_original_random_fullcell_centred_AE_limit_public X hν n i hEnd Z hZeq
  obtain ⟨B, hBI, hBound⟩ :=
    avram_agentC_original_random_fullcell_centred_L2_envelope_public X hν n i hEnd Z hZeq
  have hΔ : Tendsto (fun m : ℕ =>
      (n : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (n : ℝ))
  have hHlim : ∀ᵐ ω ∂P,
      Tendsto (fun m => |H m ω|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hZlim] with ω hz
    have hTop : Tendsto
        (fun m : ℕ => K * (|Z m ω| + (Z m ω) ^ 2 +
            (n : ℝ) / ((m : ℝ) + 1)))
        atTop (𝓝 (0 : ℝ)) := by
      convert (((hz.abs.add (hz.pow 2)).add hΔ).const_mul K) using 1 <;>
        simp [mul_add, add_assoc]
    exact squeeze_zero
      (fun m : ℕ => abs_nonneg (H m ω))
      (fun m : ℕ => by
        have herr := hError m ω
        simpa [NNReal.coe_div, NNReal.coe_add, Nat.cast_add, Nat.cast_one] using herr)
      hTop
  have hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖|H m ω|‖ ≤ K * B ω := by
    intro m
    filter_upwards [hBound] with ω hω
    have herr := hError m ω
    have hm : |Z m ω| + (Z m ω)^2 +
        ((n : ℝ) / ((m : ℝ) + 1)) ≤ B ω := hω m
    have hterm : |Z m ω| + (Z m ω)^2 +
        (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) ≤ B ω := by
      simpa [NNReal.coe_div, NNReal.coe_add, Nat.cast_add, Nat.cast_one] using hm
    simpa only [Real.norm_eq_abs, abs_abs] using
      le_trans herr (mul_le_mul_of_nonneg_left hterm hK)
  have hBI' : Integrable (fun ω => K * B ω) P := hBI.const_mul K
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      (fun ω => K * B ω) hMeas hBI' hDom hHlim)
