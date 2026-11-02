-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_taylor_small_mark_L2_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:18:25.497207+00:00
-- url     : https://prove2.me/submissions/92fffebb-dba6-4825-80d6-dca9cad5a886

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounted deterministic horizon truncation preserves the original
    controlled source jump Taylor remainder's vanishing small-mark energy. -/
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
    (hu0 : 0 ≤ u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
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
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let HD : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1 * HS p
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HD (p, z)) ^ 2) ∂X.ν ∂μ) = 0 := by
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let HD : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => ρ p.1 * HS p
  change (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
    ∫⁻ z in B n, ENNReal.ofReal ((HD (p, z)) ^ 2) ∂X.ν ∂μ) = 0
  have htail :=
    avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
      B hBm hBneg hBanti hBempty
  have hρbound (p : ℝ≥0 × Ω) : |ρ p| ≤ 1 := by
    by_cases ht : p.1 ≤ T
    · have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
      have hqtime : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht0
      have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
        calc
          Real.exp (-(q * (p.1 : ℝ))) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by linarith)
          _ = 1 := Real.exp_zero
      simpa [ρ, ht, abs_of_pos (Real.exp_pos _)] using he
    · simp [ρ, ht]
  have hpoint (p : ((ℝ≥0 × Ω) × ℝ)) :
      (HD p)^2 ≤ (HS p)^2 := by
    have hb : -1 ≤ ρ p.1 ∧ ρ p.1 ≤ 1 := abs_le.mp (hρbound p.1)
    have hp : 0 ≤ 1 + ρ p.1 := by linarith
    have hm : 0 ≤ 1 - ρ p.1 := by linarith
    have hs : (ρ p.1)^2 ≤ 1 := by
      nlinarith [mul_nonneg hp hm]
    calc
      (HD p)^2 = (ρ p.1)^2 * (HS p)^2 := by dsimp [HD]; ring
      _ ≤ 1 * (HS p)^2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg (HS p))
      _ = (HS p)^2 := by ring
  have hE (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HD (p, z)) ^ 2) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (hpoint (p,z))
  let F : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HD (p, z)) ^ 2) ∂X.ν ∂μ
  let G : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p, z)) ^ 2) ∂X.ν ∂μ
  have hFG (n : ℕ) : F n ≤ G n := hE n
  have hInf : (⨅ n, F n) ≤ (⨅ n, G n) := by
    apply le_iInf
    intro n
    exact (iInf_le F n).trans (hFG n)
  have hGzero : (⨅ n, G n) = 0 := htail
  change (⨅ n, F n) = 0
  apply le_antisymm
  · calc
      (⨅ n, F n) ≤ (⨅ n, G n) := hInf
      _ = 0 := hGzero
  · exact bot_le
