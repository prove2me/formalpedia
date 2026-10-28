-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_next_expected_le_current_mul_twoSided
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:26:58.073025+00:00
-- url     : https://prove2.me/submissions/609faaf9-d576-471d-aded-1e6d6dee80f4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_capped_lintegral_le_shifted_reward
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_trueTwoSided_expected_upper
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_true_clock_within_horizon
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_global_upper_of_caps
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (n : ℕ) :
    (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  classical
  let b : ℝ := (n : ℝ) * ε
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hindex : b + ε = (((n + 1 : ℕ) : ℝ) * ε) := by
    simp [b, Nat.cast_add, add_mul]
  let factor : ℝ≥0∞ := ∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P
  let prior : ℝ≥0∞ := ∫⁻ ω, if twoSidedExitUpTime X b ω <
      barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P
  have hcap (N : ℝ≥0) :
      (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω <
          barrierRuinTime X a ω ∧
          twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞) then
        ENNReal.ofReal ε *
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X (b + ε) ω).toReal)))
        else 0 ∂P) ≤ factor * prior := by
    let ρ : Ω → ℝ≥0∞ := fun ω => ⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
        X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)
    let σ : Ω → ℝ≥0∞ := fun ω => ⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
        X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞)
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
    let A : Set Ω := {ω | twoSidedExitUpTime X b ω <
      barrierRuinTime X a ω} ∩
      {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
    let discount : ℝ≥0 → ℝ≥0∞ := fun t =>
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
    let weight : Ω → ℝ≥0∞ := fun ω =>
      if ω ∈ A then ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
        (if ρ ω < σ ω then
          ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal))) else 0))
      else 0
    have hA : MeasurableSet A := by
      simpa only [A] using firstRecord_capped_survival_measurable_global X a b N
    have hd : Measurable discount := by
      dsimp [discount]
      fun_prop
    have hMarkov := firstRecord_capped_trueTwoSided_expected_upper
      X a b N τ rfl A rfl hA discount hd q ε (-a) weight (by
        intro ω
        by_cases hω : ω ∈ A
        · have hclock : τ ω = (twoSidedExitUpTime X b ω).toNNReal := by
            exact firstRecord_capped_clock_eq_true_clock_within_horizon
              X b N ω hω.2
          have hreward := levy_shifted_trueTwoSided_reward_eq_schedule
            X ω (twoSidedExitUpTime X b ω).toNNReal q ε (-a)
          simp only [weight, if_pos hω, discount, hclock]
          rw [← hreward]
          simp [ρ, σ, iInf_subtype, mul_assoc]
        · simp [weight, hω])
    have hPath := killed_nextRecord_capped_lintegral_le_shifted_reward
      X a b ε q ha hb hε.le N ρ σ (fun _ => rfl) (fun _ => rfl)
    have hFirst : (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) ≤ prior := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ A
      · have hclock : τ ω = (twoSidedExitUpTime X b ω).toNNReal := by
          exact firstRecord_capped_clock_eq_true_clock_within_horizon
            X b N ω hω.2
        have hs : twoSidedExitUpTime X b ω < barrierRuinTime X a ω := hω.1
        simpa [discount, hω, hs, hclock, ENNReal.ofReal_mul hε.le,
          ENNReal.coe_toNNReal_eq_toReal]
      · simp [hω]
    calc
      _ ≤ (∫⁻ ω, weight ω ∂P) := by
        simpa [weight, A, mul_assoc] using hPath
      _ ≤ (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) * factor := by
        simpa [factor, A] using hMarkov
      _ ≤ prior * factor := by gcongr
      _ = factor * prior := mul_comm _ _
  have hT : Measurable (twoSidedExitUpTime X (b + ε)) :=
    chat08_upper_passage_clock_measurable X (b + ε)
  have hw : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal))) else 0) := by
    have hR := barrierRuinTime_measurable X a
    apply Measurable.ite
    · exact measurableSet_lt hT hR
    · fun_prop
    · fun_prop
  have hglobal := killed_firstRecord_discount_global_upper_of_caps
    X a (b + ε) ε q hT hw (factor * prior) (by
      intro k
      simpa [ENNReal.ofReal_mul hε.le, and_comm, ite_and] using hcap (k : ℝ≥0))
  simpa only [factor, prior, b, hindex] using hglobal
