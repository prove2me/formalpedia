-- Prove2me | solution 1 for DegreeEligibleArithmetic.four_mul_card_eligible_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:10.008624+00:00
-- url     : https://prove2.me/submissions/dc7f4f56-1294-44eb-a432-1f687b6f86d2

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_DegreeEligibleArithmetic_card_longBad_mul_le_sum

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open DegreeEligibleArithmetic
variable {ι : Type*} [DecidableEq ι]
namespace DegreeEligibleArithmetic
theorem _root_.solution
    (n k d L : ℕ) (I X : Finset ι) (c r j : ι → ℕ)
    (hk : 2 ≤ k)
    (hcardI : k - 1 ≤ I.card)
    (hsum : ∑ i ∈ I, c i ≤ d * n)
    (hX : X.card ≤ 4 * d)
    (hstart : (boundaryBad I r k L).card ≤ L * d)
    (hfinish : (boundaryBad (I \ X) j k L).card ≤ L * d)
    (hlongScale : 16 * (d * n) ≤ k * (L + 1))
    (hboundaryScale : 16 * (L * d) ≤ k)
    (hexceptionScale : 64 * d ≤ k) :
    k ≤ 4 * (eligible I X c r j k L).card := by
  classical
  let Long := longBad I c L
  let Start := boundaryBad I r k L
  let Finish := boundaryBad (I \ X) j k L
  let P : ι → Prop := fun i ↦
    c i ≤ L ∧ r i + L ≤ k ∧ j i + L ≤ k ∧ i ∉ X
  let Good := I.filter P
  let Bad := I.filter fun i ↦ ¬ P i
  let U := ((Long ∪ Start) ∪ Finish) ∪ X
  have hpack0 := card_longBad_mul_le_sum I c L
  have hpack : Long.card * (L + 1) ≤ d * n := by
    have hpackI : Long.card * (L + 1) ≤ ∑ i ∈ I, c i := by
      simpa only [Long] using hpack0
    exact hpackI.trans hsum
  have hlong : 16 * Long.card ≤ k := by
    have hmul : (16 * Long.card) * (L + 1) ≤ k * (L + 1) := by
      calc
        (16 * Long.card) * (L + 1) =
            16 * (Long.card * (L + 1)) := by ring
        _ ≤ 16 * (d * n) := Nat.mul_le_mul_left 16 hpack
        _ ≤ k * (L + 1) := hlongScale
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hstart' : 16 * Start.card ≤ k := by
    calc
      16 * Start.card ≤ 16 * (L * d) :=
        Nat.mul_le_mul_left 16 (by simpa only [Start] using hstart)
      _ ≤ k := hboundaryScale
  have hfinish' : 16 * Finish.card ≤ k := by
    calc
      16 * Finish.card ≤ 16 * (L * d) :=
        Nat.mul_le_mul_left 16 (by simpa only [Finish] using hfinish)
      _ ≤ k := hboundaryScale
  have hX' : 16 * X.card ≤ k := by
    calc
      16 * X.card ≤ 16 * (4 * d) := Nat.mul_le_mul_left 16 hX
      _ = 64 * d := by ring
      _ ≤ k := hexceptionScale
  have hBadSub : Bad ⊆ U := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiI := hi'.1
    have hnot := hi'.2
    by_cases hx : i ∈ X
    · simp [U, hx]
    · have hiClassified : i ∈ I \ X := Finset.mem_sdiff.mpr ⟨hiI, hx⟩
      by_cases hc : c i ≤ L
      · by_cases hr : r i + L ≤ k
        · by_cases hj : j i + L ≤ k
          · exact (hnot ⟨hc, hr, hj, hx⟩).elim
          · have hj' : k < j i + L := Nat.lt_of_not_ge hj
            simp [U, Finish, boundaryBad, hiClassified, hj']
        · have hr' : k < r i + L := Nat.lt_of_not_ge hr
          simp [U, Start, boundaryBad, hiI, hr']
      · have hc' : L < c i := Nat.lt_of_not_ge hc
        simp [U, Long, longBad, hiI, hc']
  have hU : U.card ≤ Long.card + Start.card + Finish.card + X.card := by
    have h1 := Finset.card_union_le ((Long ∪ Start) ∪ Finish) X
    have h2 := Finset.card_union_le (Long ∪ Start) Finish
    have h3 := Finset.card_union_le Long Start
    dsimp [U]
    omega
  have hbad : 16 * Bad.card ≤ 4 * k := by
    have hsub := Finset.card_le_card hBadSub
    omega
  have hpartition : Good.card + Bad.card = I.card := by
    simpa [Good, Bad] using Finset.card_filter_add_card_filter_not (s := I) P
  have hgood : k ≤ 4 * Good.card := by omega
  simpa [Good, P, eligible] using hgood
end DegreeEligibleArithmetic
