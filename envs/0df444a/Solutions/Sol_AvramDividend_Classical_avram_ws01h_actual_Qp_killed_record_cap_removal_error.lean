-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_killed_record_cap_removal_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:01:34.562988+00:00
-- url     : https://prove2.me/submissions/678c6cb8-3a8f-4cb9-a06f-d360c5f7b1e7

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Removing the finite observation cap from an actual lower-killed
Esscher Qp first-record/fresh-future event costs at most exp(-pN). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (x b : ℝ) (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let τcap : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let τfull : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let Afull : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τfull z.1 →
         0 ≤ (x + b) + (X.X (τfull z.1 + u) z.1 - X.X (τfull z.1) z.1)}
     let Acap : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τcap z.1 →
         0 ≤ (x + b) + (X.X (τcap z.1 + u) z.1 - X.X (τcap z.1) z.1)}
     Qp Acap ≤ Qp Afull ∧
       Qp Afull ≤ Qp Acap + ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by
  intro Qp τcap τfull Afull Acap
  have hAgree (z : Ω × ℝ) (hr : 0 ≤ z.2)
      (hN : Real.toNNReal z.2 ≤ N)
      (hUp : twoSidedExitUpTime X b z.1 <
        (Real.toNNReal z.2 : ℝ≥0∞)) :
      τcap z.1 = τfull z.1 := by
    have hcap : twoSidedExitUpTime X b z.1 ≤ (N : ℝ≥0∞) :=
      hUp.le.trans (ENNReal.coe_le_coe.mpr hN)
    have hclock := firstRecord_capped_clock_eq_uncapped_of_le_horizon
      X b N z.1 hcap
    have h := congrArg ENNReal.toNNReal hclock
    simpa only [τcap, τfull, ENNReal.toNNReal_coe] using h
  have hSub : Acap ⊆ Afull := by
    intro z hz
    rcases hz with ⟨hr, hN, hUp, hKill, hFuture⟩
    have hτ := hAgree z hr hN hUp
    refine ⟨hr, hUp, hKill, ?_⟩
    simpa only [hτ] using hFuture
  have hCover : Afull ⊆ Acap ∪
      {z : Ω × ℝ | (N : ℝ) < z.2} := by
    intro z hz
    rcases hz with ⟨hr, hUp, hKill, hFuture⟩
    by_cases hN : Real.toNNReal z.2 ≤ N
    · left
      have hτ := hAgree z hr hN hUp
      refine ⟨hr, hN, hUp, hKill, ?_⟩
      simpa only [hτ] using hFuture
    · right
      have hNN : N < Real.toNNReal z.2 := lt_of_not_ge hN
      have hrN : (N : ℝ) < (Real.toNNReal z.2 : ℝ) :=
        NNReal.coe_lt_coe.mpr hNN
      change (N : ℝ) < z.2
      simpa only [Real.coe_toNNReal z.2 hr] using hrN
  have hTail : Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
      ENNReal.ofReal (Real.exp (-(p * (N : ℝ)))) := by
    simpa only [Qp] using
      (avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
        X θ p hθ hp N)
  constructor
  · exact measure_mono hSub
  · calc
      Qp Afull ≤ Qp (Acap ∪ {z : Ω × ℝ | (N : ℝ) < z.2}) :=
        measure_mono hCover
      _ ≤ Qp Acap + Qp {z : Ω × ℝ | (N : ℝ) < z.2} :=
        measure_union_le _ _
      _ = Qp Acap + ENNReal.ofReal (Real.exp (-(p * (N : ℝ)))) := by
        rw [hTail]
