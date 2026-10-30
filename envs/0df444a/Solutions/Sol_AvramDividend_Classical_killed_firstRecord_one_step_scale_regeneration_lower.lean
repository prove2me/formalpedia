-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:45:40.594712+00:00
-- url     : https://prove2.me/submissions/c118f01b-878d-4869-b197-9c89c2a68b69

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_global_upper_of_caps
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_chat12_capped_record_next_expected_ge_current_mul_twoSided

set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit false
set_option pp.fullNames false
/-- The lower geometric renewal step from finite stopped Markov restarts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∀ n : ℕ,
      ENNReal.ofReal (W (a - ε) / W a) *
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
  have hExit := two_sided_exit_before_ruin_integral_identity
    X hX q hq W hW a (a - ε) ha (by linarith) (by linarith)
  have hupper : a - (a - ε) = ε := by ring
  have hlower : -(a - ε) = ε - a := by ring
  rw [hupper, hlower] at hExit
  simpa only [factor, prior, next, b, hindex, hExit] using hSup
