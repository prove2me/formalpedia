-- Prove2me | solution 1 for AvramDividend.Classical.chat12_firstRecord_geometric_trueFactor_of_base
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:23:51.704391+00:00
-- url     : https://prove2.me/submissions/b484b0ca-d0cb-432a-af16-9787aae184dc

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hbase : ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ∀ n : ℕ, ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ (n + 1) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  let F : ℝ≥0∞ := (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P)
  let R (n : ℕ) : ℝ≥0∞ :=
    (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)
  have hfirst : ENNReal.ofReal ε * F ≤ R 0 := by
    simpa [F, R] using hbase
  have hstep (n : ℕ) : F * R n ≤ R (n + 1) := by
    simpa only [F, R] using
      (chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
        X q a ε ha hε n)
  have hgeom : ∀ n : ℕ,
      ENNReal.ofReal ε * F ^ (n + 1) ≤ R n := by
    intro n
    induction n with
    | zero =>
        simpa using hfirst
    | succ n ih =>
        have hpow : ENNReal.ofReal ε * F ^ ((n + 1) + 1) =
            F * (ENNReal.ofReal ε * F ^ (n + 1)) := by
          rw [pow_succ]
          ac_rfl
        have hnext : ENNReal.ofReal ε * F ^ ((n + 1) + 1) ≤
            R (n + 1) := calc
          _ = F * (ENNReal.ofReal ε * F ^ (n + 1)) := hpow
          _ ≤ F * R n := by gcongr
          _ ≤ R (n + 1) := hstep n
        simpa only [Nat.succ_eq_add_one] using hnext
  intro n
  simpa only [F, R] using hgeom n
