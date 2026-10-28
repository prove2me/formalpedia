-- Prove2me | solution 1 for CountingMatroid.Analysis.RankOneFeasibility.singletonScan_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:52:29.102957+00:00
-- url     : https://prove2.me/submissions/8ad6514a-9522-45c2-8d3d-38854a7c7049

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical





/-- INTERNAL: Under exact oracle answers the scan's single-step invariant is
that its flag records a previously found or newly tested independent singleton. -/
theorem singletonStep_val {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (found : Bool) (i : Fin n) :
    (singletonStep o₁ o₂ found i).val =
      (found || decide (M₁.Indep {i} ∧ M₂.Indep {i})) := by
  classical
  have hdecode : decode (fun j : Fin n => decide (j ∈ ({i} : Finset (Fin n)))) =
      ({i} : Set (Fin n)) := by
    ext j
    simp [decode]
  change (found || (o₁ (fun j => decide (j ∈ ({i} : Finset (Fin n)))) &&
    o₂ (fun j => decide (j ∈ ({i} : Finset (Fin n)))))) = _
  rw [h₁, h₂, hdecode]
  by_cases hfirst : M₁.Indep {i} <;> by_cases hsecond : M₂.Indep {i} <;>
    simp [hfirst, hsecond]





end CountingMatroid.Analysis.RankOneFeasibility

end
set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility
end CountingMatroid.Analysis.RankOneFeasibility
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: The bounded first-augmentation scan accepts exactly when the
two matroids have a common independent singleton, equivalently a size-one
common independent set. No shared-rank hypothesis is needed for this scan.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) :
    (singletonScan o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = 1 ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by
  classical
  have hfold (l : List (Fin n)) (found : Bool) :
      (Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) l found).val = true ↔
        found = true ∨ ∃ i ∈ l, M₁.Indep {i} ∧ M₂.Indep {i} := by
    induction l generalizing found with
    | nil => simp
    | cons i l ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons, ih,
          singletonStep_val M₁ M₂ o₁ o₂ h₁ h₂]
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
        aesop
  have hcorrect : (singletonScan o₁ o₂).val = true ↔
      ∃ I : Finset (Fin n), I.card = 1 ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    rw [singletonScan, hfold]
    simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hfirst, hsecond⟩
      exact ⟨{i}, Finset.card_singleton i,
        by simpa only [Finset.coe_singleton] using hfirst,
        by simpa only [Finset.coe_singleton] using hsecond⟩
    · rintro ⟨I, hcard, hfirst, hsecond⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨i, by simpa using hfirst, by simpa using hsecond⟩
  cases hvalue : (singletonScan o₁ o₂).val <;> simp_all
