-- Prove2me | solution 1 for AvramDividend.Classical.chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:32:05.345827+00:00
-- url     : https://prove2.me/submissions/8d43d59c-b268-496f-8995-3c35e2bfa060

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_global_upper_of_caps
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_capped_record_next_expected_ge_current_mul_twoSided


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global uncapped one-cycle lower renewal expectation, before scale normalisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ,
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
      (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  classical
  intro n
  let b : ℝ := (((n + 1 : ℕ) : ℝ) * ε)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hindex : b + ε = (((n + 2 : ℕ) : ℝ) * ε) := by dsimp [b]; push_cast; ring
  let factor : ℝ≥0∞ := ∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P
  let prior : ℝ≥0∞ := ∫⁻ ω, if twoSidedExitUpTime X b ω <
      barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P
  let next : ℝ≥0∞ := ∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P
  let oldCap (N : ℝ≥0) : ℝ≥0∞ :=
    ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P
  have hcap (N : ℝ≥0) : factor * oldCap N ≤ next := by
    exact chat12_capped_record_next_expected_ge_current_mul_twoSided
      X q a b ε ha hb hε N
  have hglobal : prior ≤ ⨆ k : ℕ, oldCap (k : ℝ≥0) := by
    apply killed_firstRecord_discount_global_upper_of_caps
      X a b ε q (chat08_upper_passage_clock_measurable X b)
      (killed_firstRecord_discount_reward_measurable X a b ε q)
    intro k
    have hk : (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (k : ℝ≥0∞) then
        (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0) else 0 ∂P) = oldCap (k : ℝ≥0) := by
      apply lintegral_congr
      intro ω
      by_cases hs : twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      · by_cases hk : twoSidedExitUpTime X b ω ≤ (k : ℝ≥0∞)
        · simp [oldCap, hs, hk]
        · simp [oldCap, hs, hk]
      · simp [oldCap, hs]
    rw [hk]
    exact le_iSup (fun j : ℕ => oldCap (j : ℝ≥0)) k
  have hSup : factor * prior ≤ next := calc
    factor * prior ≤ factor * (⨆ k : ℕ, oldCap (k : ℝ≥0)) :=
      (by gcongr)
    _ = ⨆ k : ℕ, factor * oldCap (k : ℝ≥0) := by rw [ENNReal.mul_iSup]
    _ ≤ next := iSup_le (fun k => hcap (k : ℝ≥0))
  simpa only [factor, prior, next, b, hindex] using hSup
