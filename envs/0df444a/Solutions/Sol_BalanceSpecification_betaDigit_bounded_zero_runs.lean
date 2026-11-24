-- Prove2me | solution 1 for BalanceSpecification.betaDigit_bounded_zero_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:40.497152+00:00
-- url     : https://prove2.me/submissions/6d5df25a-4bdd-4227-933f-807b98bda3c6

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Theorems.Thm_BalanceSpecification_betaDigit_zero_or_one
public import Theorems.Thm_BalanceSpecification_betaResidual_bounds
public import Theorems.Thm_BalanceSpecification_betaResidual_zero_run

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β a x R : ℝ} (hβ : 1 < β) (ha : 0 < a)
    (hax : a ≤ x) (hxR : x ≤ R) (haR : 1 + a ≤ R) (hR : (β - 1) * R ≤ 1) :
    ∃ N : ℕ, ∀ m : ℕ, ∃ i : ℕ, m ≤ i ∧ i ≤ m + N ∧ betaDigit β a x i = 1 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / a) hβ
  have hpow : R < β ^ N * a := (div_lt_iff₀ ha).mp hN
  refine ⟨N, ?_⟩
  intro m
  by_contra hnone
  push Not at hnone
  have hzero : ∀ i : ℕ, i < N → betaDigit β a x (m + i) = 0 := by
    intro i hi
    rcases betaDigit_zero_or_one β a x (m + i) with hz | ho
    · exact hz
    · exact (hnone (m + i) (by omega) (by omega) ho).elim
  have he := betaResidual_zero_run β a x m N hzero
  have hl := (betaResidual_bounds hβ ha hax hxR haR hR m).1
  have hu := (betaResidual_bounds hβ ha hax hxR haR hR (m + N)).2
  have H := mul_le_mul_of_nonneg_left hl (pow_nonneg (zero_lt_one.trans hβ).le N)
  rw [← he] at H
  exact (not_lt_of_ge (H.trans hu)) hpow
end BalanceSpecification
