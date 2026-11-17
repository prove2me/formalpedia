-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_active_clipped_firstorder_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:11:15.583419+00:00
-- url     : https://prove2.me/submissions/5db0ad98-ce76-47aa-86ae-83a015f6e89b

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_gradient_uniform
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n j : ℕ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then deriv w (x + X.X s ω - rightLimit D s ω)
        else 1)| ≤ K  := by
  classical
  obtain ⟨L, hL, hGrad⟩ :=
    avram_ga_original_finitecap_clip_gradient_uniform
      w C hC hFiniteCap hw δ hδ j
  refine ⟨max L 1, (hL.trans (le_max_left L 1)), ?_⟩
  intro m ω i
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  dsimp
  intro hi hs
  have hPost : δ ≤ Y := by
    simpa only [Y] using
      (avram_gledger20_original_strict_prefix_postpayment_floor
        X x D hD ω (ρ ω) δ (hFloor ω) s hs)
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hAY : δ / 2 ≤ Y := by linarith
  have hCoeff :
      |if Y ≤ b then deriv w Y else 1| ≤ max L 1 := by
    by_cases hy : Y ≤ b
    · have ht : |deriv w Y| ≤ L := hGrad Y ⟨hAY, hy⟩
      simpa only [if_pos hy] using ht.trans (le_max_left L 1)
    · simpa only [if_neg hy, abs_one] using (le_max_right L 1)
  have hqtime : 0 ≤ q * (s : ℝ) :=
    mul_nonneg hq (NNReal.coe_nonneg _)
  have he : Real.exp (-(q * (s : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqtime)
  have hpos : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
    (Real.exp_pos _).le
  change |Real.exp (-(q * (s : ℝ))) *
        (if Y ≤ b then deriv w Y else 1)| ≤ max L 1
  calc
    _ = Real.exp (-(q * (s : ℝ))) *
        |if Y ≤ b then deriv w Y else 1| := by
      simp only [abs_mul, abs_of_nonneg hpos]
    _ ≤ |if Y ≤ b then deriv w Y else 1| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right he (abs_nonneg _))
    _ ≤ max L 1 := hCoeff
