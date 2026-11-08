-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian12_stopped_condexp_to_positive_clock_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:29:49.948113+00:00
-- url     : https://prove2.me/submissions/618cf55b-a0a0-45af-9f4e-9355ff1ad43a

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hStoppedZero : ∀ᵐ ω ∂P,
      condExp hτstop.measurableSpace P M ω = 0) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, M ω ∂P) = 0 := by
  have hm : hτstop.measurableSpace ≤ mΩ :=
    hτstop.measurableSpace_le
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hInitialSub :
      (𝓕.rightCont 0) ≤ hτstop.measurableSpace := by
    apply hτstop.le_measurableSpace_of_const_le
    intro ω
    change (↑(0 : ℝ≥0) : WithTop ℝ≥0) ≤
      (↑(τ ω) : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (by positivity)
  have hInitialZero :
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0 := by
    calc
      condExp (𝓕.rightCont 0) P M =ᵐ[P]
        condExp (𝓕.rightCont 0) P
          (condExp hτstop.measurableSpace P M) :=
        (condExp_condExp_of_le hInitialSub hm).symm
      _ =ᵐ[P] condExp (𝓕.rightCont 0) P (fun _ => (0 : ℝ)) :=
        condExp_congr_ae hStoppedZero
      _ =ᵐ[P] (fun _ => (0 : ℝ)) := by simp
  exact
    AvramDividend.Classical.avram_gaussian11_strict_positive_stopping_clock_condexp_zero
      σ hσstop M hMI hInitialZero
