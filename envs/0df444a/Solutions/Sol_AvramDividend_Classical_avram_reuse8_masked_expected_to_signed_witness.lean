-- Prove2me | solution 1 for AvramDividend.Classical.avram_reuse8_masked_expected_to_signed_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:47:14.657398+00:00
-- url     : https://prove2.me/submissions/4bc3172f-4c41-445d-962b-a04f28fbe66e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Theorems.Thm_AvramDividend_Classical_avram_route10_signed_integrable_nonpositive_mean_centering

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (hb : 0 ≤ b)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hFI : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hExpected : ∀ k,
      (∫ ω, if σ k ω = 0 then b else F k ω ∂P) ≤ b) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      AEStronglyMeasurable (fun ω => if σ k ω = 0 then b else F k ω) P ∧
      (0 ≤ᵐ[P] fun ω => if σ k ω = 0 then b else F k ω) ∧
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then b else F k ω) ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  intro k
  let H : Ω → ℝ := fun ω => if σ k ω = 0 then b else F k ω
  have hHI : Integrable H P :=
    avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
      (σ k) (hσstop k) (F k) (hFI k) b
  have hHnonneg : 0 ≤ᵐ[P] H := by
    filter_upwards [hFnonneg k] with ω hω
    dsimp [H]
    split_ifs <;> assumption
  have hZI : Integrable (fun ω => H ω - b) P :=
    hHI.sub (integrable_const b)
  have hMean : (∫ ω, H ω - b ∂P) ≤ 0 := by
    rw [integral_sub hHI (integrable_const b)]
    have hConst : (∫ (_ : Ω), b ∂P) = b := by simp
    rw [hConst]
    exact sub_nonpos.mpr (by simpa only [H] using hExpected k)
  obtain ⟨M, B, hMI, hM0, hB, hEq⟩ :=
    avram_route10_signed_integrable_nonpositive_mean_centering
      P (fun ω => H ω - b) hZI hMean
  have hZeroI : Integrable (fun _ : Ω => (0 : ℝ)) P :=
    integrable_const 0
  have hZeroMean : (∫ (_ : Ω), (0 : ℝ) ∂P) = 0 := by simp
  refine ⟨M, (fun _ => 0), (fun _ => 0), B, (fun _ => 0),
    hHI.aestronglyMeasurable, hHnonneg, hMI, hZeroI, hZeroI,
    hM0, hZeroMean, hZeroMean, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall hB
  · exact Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ))
  · filter_upwards [] with ω
    have hEqω := hEq ω
    dsimp [H] at hEqω ⊢
    linarith
