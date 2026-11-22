-- Prove2me | solution 1 for AvramDividend.Classical.avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:57:57.529132+00:00
-- url     : https://prove2.me/submissions/892965bf-8f6b-49ac-9196-94ca597f0e73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ b C q : ℝ)
    (hδ : 0 < δ) (hb : 0 < b) (hbC : b < C) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (n m i : ℕ) (ω : Ω),
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        i < m → s < ρ ω → s + Δ ≤ ρ ω →
        |Real.exp (-(q * (s : ℝ))) *
          (if x + X.X s ω - rightLimit D s ω ≤ b
           then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
           else 0)| ≤ K := by
  let a : ℝ := min (δ / 2) (b / 2)
  have ha : 0 < a := lt_min (by linarith)
    (by linarith)
  have hab : a ≤ b := by
    dsimp [a]
    have h := min_le_right (δ / 2) (b / 2)
    linarith
  obtain ⟨K, hK⟩ :=
    avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound
      w C a b ha hbC hw
  have hKn : 0 ≤ K := le_trans (norm_nonneg _)
    (hK a ⟨le_refl a, hab⟩)
  refine ⟨K, hKn, ?_⟩
  intro n m i ω
  dsimp only
  intro hi hs hnext
  have hfloor :
      δ ≤ x + X.X
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω :=
    avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) δ (hFloor ω) _ hs
  by_cases hle :
      x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω ≤ b
  · have hmem : x + X.X
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          rightLimit D
            ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω ∈ Icc a b := by
      refine ⟨?_, hle⟩
      have h := min_le_left (δ / 2) (b / 2)
      dsimp [a]
      linarith
    have hcoeff := hK _ hmem
    have hsnonneg : 0 ≤
        (((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) : ℝ) :=
      by positivity
    have he : Real.exp (-(q *
        ((((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) : ℝ)))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hq hsnonneg]
    simp only [if_pos hle, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact le_trans (mul_le_of_le_one_left (abs_nonneg _) he)
      (by simpa only [Real.norm_eq_abs] using hcoeff)
  · simp [hle, hKn]
