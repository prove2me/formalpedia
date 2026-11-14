-- Prove2me | solution 1 for ConsistentSubmodular.exists_finite_joint_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:57.863567+00:00
-- url     : https://prove2.me/submissions/20c269c3-8ab1-49fc-8756-b25ac8917c05

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Theorems.Thm_ConsistentSubmodular_exists_joint_rounding

section

open scoped BigOperators
open ConsistentSubmodular

theorem solution {n : ℕ} {τ ι ε : Type*}
    [Fintype τ] [Fintype ι] [Fintype ε]
    (z : τ → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (g : ι → Objective n) (left right : ι → τ) (edgeLeft edgeRight : ε → τ)
    (κ L M a b R pSize pValue pCost : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (hcap : ∀ i e, (g i).value {e} - (g i).value ∅ ≤ L)
    (hmean : ∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
      (g i).value ≤ M)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * L * M)) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (Fintype.card τ : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ S : τ → Finset (Fin n),
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ κ + b) ∧
      (∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
        (g i).value - a ≤ (g i).value (S (left i) ∩ S (right i))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by
  classical
  let E := Fintype.equivFin τ
  obtain ⟨S, hzero, hone, hcard, hval, hcost, hequal⟩ := exists_joint_rounding
    (fun t => z (E.symm t)) (fun t => hz (E.symm t))
    g (fun i => E (left i)) (fun i => E (right i))
    (fun j => E (edgeLeft j)) (fun j => E (edgeRight j))
    κ L M a b R pSize pValue pCost ha hb hb2 hR hL hM
    (fun t => hsize (E.symm t)) hcap (by simpa using hmean)
    hsizeBudget hvalueBudget (by simpa using hcostBudget) hbudget
  refine ⟨fun t => S (E t), ?_, ?_, ?_, ?_, hcost, ?_⟩
  · intro t e h
    apply hzero (E t) e
    simpa using h
  · intro t e h
    apply hone (E t) e
    simpa using h
  · intro t
    exact hcard (E t)
  · simpa using hval
  · intro s t h
    apply hequal (E s) (E t)
    simpa using h

end
