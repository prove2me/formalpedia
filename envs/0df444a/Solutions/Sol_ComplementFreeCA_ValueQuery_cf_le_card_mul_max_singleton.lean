-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.cf_le_card_mul_max_singleton
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:40:50.88498+00:00
-- url     : https://prove2.me/submissions/1ed00609-cb05-474a-83e3-df897f08086c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery

theorem solution {m : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsCFValuation v)
    (T : Finset (Fin m)) (c : Fin m) (hc : c ∈ T) (hmax : ∀ j ∈ T, v {j} ≤ v {c}) :
    v T ≤ ∑ j ∈ T, v {j} ∧ ∑ j ∈ T, v {j} ≤ (T.card : ℝ) * v {c} := by
  have hsum : ∀ S : Finset (Fin m), v S ≤ ∑ j ∈ S, v {j} := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa only [sum_empty] using le_of_eq hv.1
    | @insert a S ha ih =>
      have h := (hv.2.2 {a} S).trans (add_le_add le_rfl ih)
      simpa only [singleton_union, sum_insert ha] using h
  refine ⟨hsum T, ?_⟩
  calc
    ∑ j ∈ T, v {j} ≤ ∑ j ∈ T, v {c} := sum_le_sum hmax
    _ = _ := by simp
