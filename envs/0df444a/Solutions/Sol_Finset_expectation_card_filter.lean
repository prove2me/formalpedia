-- Prove2me | solution 1 for Finset.expectation_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:51.498457+00:00
-- url     : https://prove2.me/submissions/f11aa9ed-7c19-4923-a833-eb2d1d942820

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution {ι : Type*} (I : Finset ι) (E : ι → Finset α → Prop)
    [∀ i, DecidablePred (E i)] :
    ∑ B ∈ U.powerset, U.bernoulliWeight p B * (#{i ∈ I | E i B} : ℝ) =
      ∑ i ∈ I, U.bernoulliProb p (E i) := by
  simp_rw [card_filter, Nat.cast_sum, mul_sum, bernoulliProb, sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun B _ => by split_ifs <;> simp
end Finset
