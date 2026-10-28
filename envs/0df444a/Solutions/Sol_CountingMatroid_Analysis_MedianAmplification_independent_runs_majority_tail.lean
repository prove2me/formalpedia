-- Prove2me | solution 1 for CountingMatroid.Analysis.MedianAmplification.independent_runs_majority_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:58:59.026014+00:00
-- url     : https://prove2.me/submissions/039008aa-ed0f-499a-86c3-ece40a49b9ee

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_IndependentRunsCore
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: Expanding a PMF bind inside an ENNReal weighted sum. -/
private theorem weighted_bind {α β : Type} (p : PMF α) (f : α → PMF β)
    (w : β → ENNReal) :
    (∑' y, (p.bind f) y * w y) =
      ∑' x, p x * ∑' y, f x y * w y := by
  calc
    _ = ∑' y, ∑' x, (p x * f x y) * w y := by
      simp only [PMF.bind_apply, ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, p x * (f x y * w y) := by
      rw [ENNReal.tsum_comm]
      simp only [mul_assoc]
    _ = _ := by simp only [ENNReal.tsum_mul_left]

/-- INTERNAL: Expanding a PMF map inside an ENNReal weighted sum. -/
private theorem weighted_map {α β : Type} (p : PMF α) (f : α → β)
    (w : β → ENNReal) :
    (∑' y, (p.map f) y * w y) = ∑' x, p x * w (f x) := by
  change (∑' y, (p.bind (pure ∘ f)) y * w y) = _
  rw [weighted_bind]
  simp only [Function.comp_def]
  congr 1
  funext x
  congr 1
  rw [tsum_eq_single (f x)]
  · change (PMF.pure (f x)) (f x) * w (f x) = w (f x)
    rw [PMF.pure_apply_self, one_mul]
  · intro y hy
    change (PMF.pure (f x)) y * w y = 0
    rw [PMF.pure_apply_of_ne (f x) y hy, zero_mul]

/-- INTERNAL: The exponential moment of the count of bad independent runs factors. -/
private theorem independentRuns_moment (q : PMF ℚ) (bad : ℚ → Bool) (m : ℕ) :
    (∑' xs, (independentRuns q m) xs * (2 : ENNReal) ^ xs.countP bad) =
      (∑' x, q x * (if bad x then (2 : ENNReal) else 1)) ^ m := by
  induction m with
  | zero =>
      simp only [pow_zero, independentRuns]
      change (∑' xs, (PMF.pure ([] : List ℚ)) xs *
        (2 : ENNReal) ^ xs.countP bad) = 1
      rw [tsum_eq_single []]
      · simp
      · intro xs hxs
        rw [PMF.pure_apply_of_ne ([] : List ℚ) xs hxs, zero_mul]
  | succ m ih =>
      change (∑' ys, (q.bind fun x =>
        (independentRuns q m).map (List.cons x)) ys *
        (2 : ENNReal) ^ ys.countP bad) = _
      rw [weighted_bind]
      simp_rw [weighted_map]
      have hinner (x : ℚ) :
          (∑' xs, (independentRuns q m) xs *
            (2 : ENNReal) ^ (x :: xs).countP bad) =
          (if bad x then (2 : ENNReal) else 1) *
            (∑' xs, (independentRuns q m) xs *
              (2 : ENNReal) ^ xs.countP bad) := by
        cases h : bad x <;>
          simp [h, pow_succ, mul_comm, mul_assoc]
        rw [ENNReal.tsum_mul_left]
      simp only [hinner, ih, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      simp [pow_succ, mul_comm]

/-- INTERNAL: The one-run exponential moment is at most five quarters. -/
private theorem one_run_moment_le (q : PMF ℚ) (bad : ℚ → Bool)
    (hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal)) :
    (∑' x, q x * (if bad x then (2 : ENNReal) else 1)) ≤
      (5 / 4 : ENNReal) := by
  have hfactor :
      (∑' x, q x * (if bad x then (2 : ENNReal) else 1)) =
        1 + q.toOuterMeasure {x | bad x = true} := by
    calc
      _ = ∑' x, (q x + ({x | bad x = true} : Set ℚ).indicator q x) := by
        congr 1
        funext x
        cases h : bad x <;> simp [Set.indicator, h, mul_two]
      _ = _ := by rw [ENNReal.tsum_add, PMF.tsum_coe, PMF.toOuterMeasure_apply]
  rw [hfactor]
  calc
    _ ≤ 1 + (1 / 4 : ENNReal) := by simpa [add_comm] using add_le_add_left hq 1
    _ = (5 / 4 : ENNReal) := by
      have h4 : (4 : ENNReal) / 4 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
      calc
        _ = (4 : ENNReal) / 4 + 1 / 4 := by rw [h4]
        _ = ((4 : ENNReal) + 1) / 4 := ENNReal.add_div.symm
        _ = _ := by norm_num



end CountingMatroid.Analysis.MedianAmplification

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · closed `independent_runs_majority_tail` by the factored exponential moment and a discrete Markov estimate.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: The finite product tail estimate for a strict majority of bad runs.
TEXLINE: main.tex:1448-1458 -/
theorem solution (q : PMF ℚ) (bad : ℚ → Bool) (b : ℕ)
    (hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal)) :
    (independentRuns q (10 * b + 1)).toOuterMeasure
      {xs | (10 * b + 1) / 2 + 1 ≤ xs.countP bad} ≤
      (1 / 2 : ENNReal) ^ b := by
  have hk : (10 * b + 1) / 2 + 1 = 5 * b + 1 := by omega
  simp only [hk]
  let p := independentRuns q (10 * b + 1)
  let k := 5 * b + 1
  let event : Set (List ℚ) := {xs | k ≤ xs.countP bad}
  have hmarkov : p.toOuterMeasure event * (2 : ENNReal) ^ k ≤
      ∑' xs, p xs * (2 : ENNReal) ^ xs.countP bad := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro xs
    by_cases hx : xs ∈ event
    · rw [Set.indicator_of_mem hx]
      exact mul_le_mul_right (pow_le_pow_right₀ (by norm_num : (1 : ENNReal) ≤ 2) hx) _
    · rw [Set.indicator_of_notMem hx, zero_mul]
      exact zero_le
  have hpow : (2 : ENNReal) ^ k * (1 / 2 : ENNReal) ^ k = 1 := by
    rw [← mul_pow]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have htail : p.toOuterMeasure event ≤
      (5 / 4 : ENNReal) ^ (10 * b + 1) * (1 / 2 : ENNReal) ^ k := by
    calc
      _ = p.toOuterMeasure event * ((2 : ENNReal) ^ k * (1 / 2 : ENNReal) ^ k) := by
        rw [hpow, mul_one]
      _ = (p.toOuterMeasure event * (2 : ENNReal) ^ k) * (1 / 2 : ENNReal) ^ k := by
        rw [mul_assoc]
      _ ≤ (∑' xs, p xs * (2 : ENNReal) ^ xs.countP bad) *
          (1 / 2 : ENNReal) ^ k := mul_le_mul_left hmarkov _
      _ ≤ _ := by
        rw [show (∑' xs, p xs * (2 : ENNReal) ^ xs.countP bad) =
          (∑' x, q x * (if bad x then (2 : ENNReal) else 1)) ^ (10 * b + 1) from
            independentRuns_moment q bad _]
        exact mul_le_mul_left
          (pow_le_pow_left₀ (zero_le : (0 : ENNReal) ≤ _) (one_run_moment_le q bad hq) _) _
  change p.toOuterMeasure event ≤ (1 / 2 : ENNReal) ^ b
  exact htail.trans (by
    change (5 / 4 : ENNReal) ^ (10 * b + 1) * (1 / 2 : ENNReal) ^ (5 * b + 1) ≤
      (1 / 2 : ENNReal) ^ b
    have hbase : (5 / 4 : ENNReal) ^ 10 * (1 / 2 : ENNReal) ^ 5 ≤
        (1 / 2 : ENNReal) := by
      have hfin : (5 / 4 : ENNReal) ^ 10 * (1 / 2 : ENNReal) ^ 5 ≠ ⊤ :=
        ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num)))
          (ENNReal.pow_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num)))
      apply (ENNReal.toReal_le_toReal hfin
        (ENNReal.div_ne_top (by norm_num) (by norm_num))).1
      norm_num
    have hsmall : (5 / 4 : ENNReal) * (1 / 2 : ENNReal) ≤ 1 := by
      have hfin : (5 / 4 : ENNReal) * (1 / 2 : ENNReal) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
      apply (ENNReal.toReal_le_toReal hfin (by norm_num)).1
      norm_num
    calc
      _ = ((5 / 4 : ENNReal) ^ 10 * (1 / 2 : ENNReal) ^ 5) ^ b *
          ((5 / 4 : ENNReal) * (1 / 2 : ENNReal)) := by
        rw [pow_add, pow_add, pow_mul, pow_mul, mul_pow]
        simp only [pow_one]
        ac_rfl
      _ ≤ (1 / 2 : ENNReal) ^ b * 1 := by
        gcongr
      _ = _ := by rw [mul_one])
