-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_full_actual_discounted_signed_right_payment_correction_summable_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:38:47.986754+00:00
-- url     : https://prove2.me/submissions/0361716d-e497-46ca-bb06-bb3705cfb5d0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The entire actual chronological right-payment nonlinear correction is
absolutely summable and nonpositive under its stated localized secant and
pointwise hjump bounds; diffuse dividends remain separate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (A : Set ℝ)
    (hA : A = {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (L : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSecant : ∀ s : A, |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| ≤
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) :
    Summable (fun s : A =>
      Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ∧
    (∑' s : A,
      Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  let B : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let δ : A → ℝ := fun s =>
    rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω
  let U : A → ℝ := fun s =>
    riskProcess X x D ((s : ℝ).toNNReal) ω
  let K : A → ℝ := fun s => δ s + w (U s - δ s) - w (U s)
  have hSupport :
      B.Countable ∧ Summable (fun s : B =>
        rightLimit D ((s : ℝ).toNNReal) ω -
          D ((s : ℝ).toNNReal) ω) :=
    avram_wave4_04b_full_right_payment_jump_support_summable D hD ω T
  have hB_eqA : B = A := hA.symm
  have hδ : Summable δ := by
    have hs := hSupport.2
    rw [hB_eqA] at hs
    exact hs
  have hWindow (s : A) :
      (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (T : ℝ) := by
    have hs : (s : ℝ) ∈ B := by
      rw [hB_eqA]
      exact s.property
    exact ⟨hs.1, hs.2.1⟩
  have hKbound (s : A) : |K s| ≤ L * δ s := by
    exact hSecant s
  have hWeighted : Summable (fun s : A => L * δ s) :=
    hδ.mul_left L
  have hCorrSum :
      Summable (fun s : A =>
        Real.exp (-(q * (s : ℝ))) * K s) := by
    apply Summable.of_norm_bounded hWeighted
    intro s
    have hs : 0 ≤ (s : ℝ) := (hWindow s).1
    have hE0 : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hE1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hqtime : 0 ≤ q * (s : ℝ) := mul_nonneg hq hs
      linarith
    calc
      ‖Real.exp (-(q * (s : ℝ))) * K s‖ =
          Real.exp (-(q * (s : ℝ))) * |K s| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hE0]
      _ ≤ 1 * |K s| :=
        mul_le_mul_of_nonneg_right hE1 (abs_nonneg _)
      _ = |K s| := one_mul _
      _ ≤ L * δ s := hKbound s
  have hTime (s : A) : ((s : ℝ).toNNReal : ℝ≥0) ≤ T := by
    have hCoe : (((s : ℝ).toNNReal : ℝ≥0) : ℝ) = (s : ℝ) :=
      Real.coe_toNNReal (s : ℝ) (hWindow s).1
    exact_mod_cast (show (((s : ℝ).toNNReal : ℝ≥0) : ℝ) ≤ (T : ℝ) from by
      simpa only [hCoe] using (hWindow s).2)
  have hKnonpos (s : A) : K s ≤ 0 := by
    have hJ := hjump ((s : ℝ).toNNReal) (hTime s)
    change δ s ≤ w (U s) - w (U s - δ s) at hJ
    dsimp [K]
    linarith
  have hNonpos :
      (∑' s : A, Real.exp (-(q * (s : ℝ))) * K s) ≤ 0 := by
    apply tsum_nonpos
    intro s
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) (hKnonpos s)
  change Summable (fun s : A =>
    Real.exp (-(q * (s : ℝ))) * K s) ∧
    (∑' s : A, Real.exp (-(q * (s : ℝ))) * K s) ≤ 0
  exact ⟨hCorrSum, hNonpos⟩
