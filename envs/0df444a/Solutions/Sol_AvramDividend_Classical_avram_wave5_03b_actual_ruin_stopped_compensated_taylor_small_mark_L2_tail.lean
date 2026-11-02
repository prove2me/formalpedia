-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:28:48.653966+00:00
-- url     : https://prove2.me/submissions/a65cff4e-8614-4c90-abd8-875773e6adb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual ruin-stopped, prepayment controlled Lévy Taylor remainder has
vanishing intensity quadratic mass on all shrinking negative jump-mark sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by
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
  change (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
    ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) = 0
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨K, hK, hpoint⟩ :=
    avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
      X w a b u v δ hw1 hw_cont hw_neg hau huv hvb hu0 hδ hδone hband
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  let S (n : ℕ) : ℝ≥0∞ := ∫⁻ z in B n, f z ∂X.ν
  let A (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ
  have hfmeas : Measurable f := by fun_prop
  have hfint : (∫⁻ z, f z ∂X.ν) ≠ ⊤ := ne_of_lt X.ν_integrable
  have hSzero : (⨅ n : ℕ, S n) = 0 := by
    exact avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
      X.ν f hfmeas hfint B hBm hBanti hBempty
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  have hmin (z : ℝ) : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hH (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      (H (p,z)) ^ 2 ≤ K * min 1 (z ^ 2) := by
    by_cases hb : Y p ∈ Icc (u + δ) v
    · have hb' : u + δ ≤ Y p ∧ Y p ≤ v := hb
      have hExpr : H (p,z) =
          w (Y p + z) - w (Y p) -
            (if -1 < z then z * deriv w (Y p) else 0) := by
        simp [H, Set.mem_Icc, hb']
      rw [hExpr]
      exact hpoint (Y p) hb z hz
    · have hb' : ¬ (u + δ ≤ Y p ∧ Y p ≤ v) := hb
      have hExpr : H (p,z) = 0 := by
        simp [H, Set.mem_Icc, hb']
      simpa [hExpr] using (mul_nonneg hK (hmin z))
  have hHS (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      (HS (p,z)) ^ 2 ≤ K * min 1 (z ^ 2) := by
    by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · simpa [HS, hs] using hH p z hz
    · simpa [HS, hs] using (mul_nonneg hK (hmin z))
  have hbound (n : ℕ) :
      A n ≤ (μ Set.univ * ENNReal.ofReal K) * S n := by
    have hpoint' (p : ℝ≥0 × Ω) (z : ℝ) (hz : z ∈ B n) :
        ENNReal.ofReal ((HS (p,z)) ^ 2) ≤
        ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) := by
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (hHS p z (hBneg n hz))
    have hinner (p : ℝ≥0 × Ω) :
        (∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν) ≤
          ENNReal.ofReal K *
            (∫⁻ z in B n, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
      calc
        (∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν) ≤
          ∫⁻ z in B n, ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              exact hpoint' p z hz
        _ = _ := lintegral_const_mul _ hνmeas
    calc
      A n ≤
          ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal K *
            (∫⁻ z in B n, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) ∂μ :=
        lintegral_mono hinner
      _ = μ Set.univ * (ENNReal.ofReal K * S n) := by
        simp [S, f, mul_comm]
      _ = (μ Set.univ * ENNReal.ofReal K) * S n := by
        rw [mul_assoc]
  change (⨅ n : ℕ, A n) = 0
  apply le_antisymm _ bot_le
  calc
    (⨅ n : ℕ, A n) ≤
        (⨅ n : ℕ, (μ Set.univ * ENNReal.ofReal K) * S n) :=
      iInf_mono hbound
    _ = (μ Set.univ * ENNReal.ofReal K) * (⨅ n : ℕ, S n) := by
      by_cases hc : μ Set.univ * ENNReal.ofReal K = 0
      · simp [hc]
      · rw [ENNReal.mul_iInf_of_ne hc
          (ne_of_lt (ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top))]
    _ = 0 := by simp [hSzero]
