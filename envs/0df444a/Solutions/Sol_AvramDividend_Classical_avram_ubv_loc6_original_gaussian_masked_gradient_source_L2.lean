-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:11:08.453444+00:00
-- url     : https://prove2.me/submissions/2529ebf0-bfd4-4918-8e40-45e48259bcf4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual Gaussian source X.σ times the masked original pre-payment
    gradient is predictable and has finite square energy on the same finite
    right-continuous predictable measure, without changing sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Measurable[𝓕.rightCont.predictable] G ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ := by
  dsimp only
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hH := (avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
    X x D hD w a b u v hw hau huv hvb μ hμ).1
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨M, hM, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b u v hw1 hau huv hvb
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc u v
    then deriv w (Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1) else 0
  have hHabs (p : ℝ≥0 × Ω) : |H p| ≤ M := by
    by_cases hp : Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc u v
    · dsimp [H]
      rw [if_pos hp]
      exact hderiv _ hp.1 hp.2
    · dsimp [H]
      rw [if_neg hp]
      simpa using hM
  let K : ℝ := |X.σ| * M
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) hM
  have hGabs (p : ℝ≥0 × Ω) : |X.σ * H p| ≤ K := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hHabs p) (abs_nonneg _)
  have hGsq (p : ℝ≥0 × Ω) : (X.σ * H p) ^ 2 ≤ K ^ 2 := by
    let z : ℝ := X.σ * H p
    have hz : |z| ≤ K := hGabs p
    have hm : 0 ≤ (K - |z|) * (K + |z|) :=
      mul_nonneg (sub_nonneg.mpr hz) (add_nonneg hK (abs_nonneg z))
    have hs : |z| ^ 2 = z ^ 2 := by rw [sq_abs]
    change z ^ 2 ≤ K ^ 2
    nlinarith [hm, hs]
  refine ⟨?_, ?_⟩
  · exact (measurable_const.mul hH : Measurable (fun p => X.σ * H p))
  · have hf : μ Set.univ * ENNReal.ofReal (K ^ 2) < ⊤ :=
      ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top
    calc
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((X.σ * H p) ^ 2) ∂μ) ≤
        ∫⁻ _ : ℝ≥0 × Ω, ENNReal.ofReal (K ^ 2) ∂μ := by
          apply lintegral_mono
          intro p
          exact ENNReal.ofReal_le_ofReal (hGsq p)
      _ = μ Set.univ * ENNReal.ofReal (K ^ 2) := by simp [mul_comm]
      _ < ⊤ := hf
