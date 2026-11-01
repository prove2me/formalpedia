-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_original_controlled_negative_mark_tail_energy_inf_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:28:23.170676+00:00
-- url     : https://prove2.me/submissions/4aeff841-1061-4310-bc4a-c98944b7a117

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_controlled_negative_strip_quadratic_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Uniform L² energy of controlled source jump kernels vanishes on every decreasing
sequence of measurable negative-mark regions with empty intersection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
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
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  change (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
    ∫⁻ z in B n, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) = 0
  obtain ⟨K, hK, hstrip⟩ :=
    avram_wave4_04_original_controlled_negative_strip_quadratic_budget
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  let S (n : ℕ) : ℝ≥0∞ := ∫⁻ z in B n, f z ∂X.ν
  let A (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ
  have hfmeas : Measurable f := by fun_prop
  have hfint : (∫⁻ z, f z ∂X.ν) ≠ ⊤ := ne_of_lt X.ν_integrable
  have hSzero : (⨅ n : ℕ, S n) = 0 := by
    exact avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
      X.ν f hfmeas hfint B hBm hBanti hBempty
  have hA (n : ℕ) :
      A n ≤ (μ Set.univ * ENNReal.ofReal K) * S n := by
    simpa only [A, S, f, mul_assoc] using hstrip (B n) (hBm n) (hBneg n)
  change (⨅ n : ℕ, A n) = 0
  apply le_antisymm _ bot_le
  calc
    (⨅ n : ℕ, A n) ≤
        (⨅ n : ℕ, (μ Set.univ * ENNReal.ofReal K) * S n) :=
      iInf_mono hA
    _ = (μ Set.univ * ENNReal.ofReal K) * (⨅ n : ℕ, S n) := by
      by_cases hc : μ Set.univ * ENNReal.ofReal K = 0
      · simp [hc]
      · rw [ENNReal.mul_iInf_of_ne hc
          (ne_of_lt (ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top))]
    _ = 0 := by simp [hSzero]
