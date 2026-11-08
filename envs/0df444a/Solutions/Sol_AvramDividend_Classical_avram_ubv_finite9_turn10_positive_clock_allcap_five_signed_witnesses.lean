-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:46:01.947611+00:00
-- url     : https://prove2.me/submissions/9b3ffdc2-c081-4e0c-ba02-c3c540260a9d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any probability-weighted conditional upper bound on the positive-clock
event admits the five-component centred signed certificate, including an
arbitrary infinite cap in downstream original-process applications. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hzeroMeas : MeasurableSet {ω : Ω | σ ω = 0})
    (hFI : Integrable F P)
    (hpositive : (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ ω = 0 then b else F ω) ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  classical
  let Mask : Ω → ℝ := fun ω => if σ ω = 0 then b else F ω
  have hMaskI : Integrable Mask P := by
    let Z : Set Ω := {ω : Ω | σ ω = 0}
    have hMaskEq : Mask = fun ω =>
        Z.indicator (fun _ => b) ω + Zᶜ.indicator F ω := by
      funext ω
      by_cases hz : σ ω = 0 <;> simp [Mask, Z, Set.indicator, hz]
    rw [hMaskEq]
    exact ((integrable_const b).indicator (show MeasurableSet Z from hzeroMeas)).add
      (hFI.indicator (show MeasurableSet Zᶜ from hzeroMeas.compl))
  have hPosMask :
      (∫ ω in {ω : Ω | σ ω ≠ 0}, Mask ω ∂P) ≤
        b * (P {ω : Ω | σ ω ≠ 0}).toReal := by
    have hEq : (∫ ω in {ω : Ω | σ ω ≠ 0}, Mask ω ∂P) =
        (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) := by
      exact setIntegral_congr_fun hzeroMeas.compl
        (by intro ω hω; simp only [Set.mem_setOf_eq] at hω; simp [Mask, hω])
    exact hEq.trans_le hpositive
  have hMean : (∫ ω, Mask ω ∂P) ≤ b :=
    avram_ubv_finite9_turn10_clock_partition_mean_upper
      b σ Mask hzeroMeas hMaskI (by intro ω hz; simp [Mask, hz]) hPosMask
  let Mc : Ω → ℝ := fun ω => Mask ω - (∫ ω, Mask ω ∂P)
  have hMcI : Integrable Mc P := hMaskI.sub (integrable_const _)
  have hMcZero : (∫ ω, Mc ω ∂P) = 0 := by
    dsimp [Mc]
    rw [integral_sub hMaskI (integrable_const _)]
    simp
  refine ⟨Mc, (fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0),
    hMcI, integrable_const (0 : ℝ), integrable_const (0 : ℝ), hMcZero,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Filter.Eventually.of_forall (fun _ => le_refl 0)
  · exact Filter.Eventually.of_forall (fun _ => le_refl 0)
  · exact Filter.Eventually.of_forall (by
      intro ω
      dsimp [Mc, Mask]
      simp only [add_zero]
      linarith)
