-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:31:11.827337+00:00
-- url     : https://prove2.me/submissions/fc6d11e6-767f-4942-9aa9-53951a94cb1a

import Mathlib
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
/-- The complete *pre-ruin* actual right-payment correction has its correct
chronological sign, including time zero and excluding terminal ruin payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (A : Set ℝ)
    (hA : A = {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (L : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSecant : ∀ s : A,
      |(rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω)| ≤
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) :
    Summable (fun s : A =>
      Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
          w (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
          w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ∧
    (∑' s : A, Real.exp (-(q * (s : ℝ))) *
      ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  let B : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let C : Set ℝ :=
    {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let δ : A → ℝ := fun s =>
    rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω
  let U : A → ℝ := fun s =>
    riskProcess X x D ((s : ℝ).toNNReal) ω
  let K : A → ℝ := fun s => δ s + w (U s - δ s) - w (U s)
  have hC_eqA : C = A := hA.symm
  have hMem (s : A) : (s : ℝ) ∈ C := by
    rw [hC_eqA]
    exact s.property
  have hPay (s : A) :
      ((s : ℝ).toNNReal = 0 ∨
        (((s : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) := by
    have hp := (hMem s).1
    change (s : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {u : ℝ | ENNReal.ofReal u < ruinTime X x D ω}) at hp
    rcases hp.2 with hzero | hlt
    · left
      have hz : (s : ℝ) = 0 := hzero
      simp [hz]
    · right
      change (((s : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) <
        ruinTime X x D ω at hlt
      exact hlt
  have hWindow (s : A) :
      (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (T : ℝ) := by
    have hp := (hMem s).1
    change (s : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {u : ℝ | ENNReal.ofReal u < ruinTime X x D ω}) at hp
    exact ⟨hp.1, (hMem s).2.1⟩
  have hInB (s : A) : (s : ℝ) ∈ B :=
    ⟨(hWindow s).1, (hWindow s).2, (hMem s).2.2⟩
  let f : A → B := fun s => ⟨s.1, hInB s⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun z : B => (z : ℝ)) hst
  have hSupport :
      B.Countable ∧ Summable (fun s : B =>
        rightLimit D ((s : ℝ).toNNReal) ω -
          D ((s : ℝ).toNNReal) ω) :=
    avram_wave4_04b_full_right_payment_jump_support_summable D hD ω T
  have hδ : Summable δ := by
    have hs := hSupport.2.comp_injective hf
    change Summable δ at hs
    exact hs
  have hKbound (s : A) : |K s| ≤ L * δ s := by
    exact hSecant s
  have hWeighted : Summable (fun s : A => L * δ s) :=
    hδ.mul_left L
  have hCorrSum :
      Summable (fun s : A => Real.exp (-(q * (s : ℝ))) * K s) := by
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
  have hKnonpos (s : A) : K s ≤ 0 := by
    have hJ := hjump ((s : ℝ).toNNReal) (hPay s)
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
