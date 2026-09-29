-- Prove2me | solution 1 for Freiman.lower_guard_checks_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T15:58:05.595023+00:00
-- url     : https://prove2.me/submissions/762e63eb-e3d6-418a-ad58-19b4246afa01

import Definitions.Def_Freiman_lowerWordGuardData
import Mathlib.Data.Fintype.Defs

open Freiman

def decidableForallBool
    (P : Bool → Prop)
    [Decidable (P false)] [Decidable (P true)] :
    Decidable (∀ b : Bool, P b) :=
  decidable_of_iff (P false ∧ P true) Bool.forall_bool.symm

def guardRight (c : LowerGuardCase) (l : LowerLabel) (right : Bool) : Prop :=
  let old := lowerSide c.before right
  let ext := if right then l.2 else l.1.reverse
  (lowerGuardState (old++ext) = [3,1,3] → ext ≠ [] →
    c.mixed = false ∧ l = ([2],[3]) ∧ right = true ∧ lowerGuardSuffix old [3,1] = true) ∧
  (lowerGuardState (old++ext) = [3,1,3,1] → ext ≠ [] → old = [3,1,3] ∧ ext = [1]) ∧
  (old ∈ [[3,1,3],[3,1,3,1]] → lowerGuardState (old++ext) ∈ [[3,1,3],[3,1,3,1]] →
    l ∈ lowerGuardShortLabels)

def guardRightDecidable (c : LowerGuardCase) (l : LowerLabel) (right : Bool) : Decidable (guardRight c l right) := by
  unfold guardRight
  cases right <;> dsimp
  · let dA : Decidable (lowerGuardState (lowerSide c.before false ++ l.1.reverse) = [3,1,3] →
        l.1.reverse ≠ [] → c.mixed = false ∧ l = ([2],[3]) ∧ false = true ∧ lowerGuardSuffix (lowerSide c.before false) [3,1] = true) := inferInstance
    let dB : Decidable (lowerGuardState (lowerSide c.before false ++ l.1.reverse) = [3,1,3,1] →
        l.1.reverse ≠ [] → lowerSide c.before false = [3,1,3] ∧ l.1.reverse = [1]) := inferInstance
    let dC : Decidable (lowerSide c.before false ∈ [[3,1,3],[3,1,3,1]] →
        lowerGuardState (lowerSide c.before false ++ l.1.reverse) ∈ [[3,1,3],[3,1,3,1]] →
          l ∈ lowerGuardShortLabels) := inferInstance
    exact @instDecidableAnd _ _ dA (@instDecidableAnd _ _ dB dC)
  · let dA : Decidable (lowerGuardState (lowerSide c.before true ++ l.2) = [3,1,3] →
        l.2 ≠ [] → c.mixed = false ∧ l = ([2],[3]) ∧ true = true ∧ lowerGuardSuffix (lowerSide c.before true) [3,1] = true) := inferInstance
    let dB : Decidable (lowerGuardState (lowerSide c.before true ++ l.2) = [3,1,3,1] →
        l.2 ≠ [] → lowerSide c.before true = [3,1,3] ∧ l.2 = [1]) := inferInstance
    let dC : Decidable (lowerSide c.before true ∈ [[3,1,3],[3,1,3,1]] →
        lowerGuardState (lowerSide c.before true ++ l.2) ∈ [[3,1,3],[3,1,3,1]] →
          l ∈ lowerGuardShortLabels) := inferInstance
    exact @instDecidableAnd _ _ dA (@instDecidableAnd _ _ dB dC)

def guardRightNF (c : LowerGuardCase) (l : LowerLabel) : Prop :=
  guardRight c l false ∧ guardRight c l true

def guardRightNFDecidable (c : LowerGuardCase) (l : LowerLabel) : Decidable (guardRightNF c l) :=
  @instDecidableAnd _ _ (guardRightDecidable c l false) (guardRightDecidable c l true)

def guardLabelNF (c : LowerGuardCase) (l : LowerLabel) : Prop :=
  (∀ d ∈ l.1++l.2, (d:ℕ) ≤ 3) ∧ (l.1 ≠ [] ∨ l.2 ≠ []) ∧
  lowerGuardSafe (c.before.1++l.1.reverse) = true ∧
  lowerGuardSafe (c.before.2++l.2) = true ∧ guardRightNF c l

def guardLabelNFDecidable (c : LowerGuardCase) (l : LowerLabel) : Decidable (guardLabelNF c l) := by
  unfold guardLabelNF
  let d1 : Decidable (∀ d ∈ l.1++l.2, (d:ℕ) ≤ 3) := inferInstance
  let d2 : Decidable (l.1 ≠ [] ∨ l.2 ≠ []) := inferInstance
  let d3 : Decidable (lowerGuardSafe (c.before.1++l.1.reverse) = true) := inferInstance
  let d4 : Decidable (lowerGuardSafe (c.before.2++l.2) = true) := inferInstance
  let d5 : Decidable (guardRightNF c l) := guardRightNFDecidable c l
  exact @instDecidableAnd _ _ d1 (@instDecidableAnd _ _ d2 (@instDecidableAnd _ _ d3 (@instDecidableAnd _ _ d4 d5)))

def guardLabelsNF (c : LowerGuardCase) : Prop := List.Forall (guardLabelNF c) c.labels

def guardLabelsNFDecidable (c : LowerGuardCase) : Decidable (guardLabelsNF c) := by
  unfold guardLabelsNF
  letI : DecidablePred (fun l => guardLabelNF c l) := fun l => guardLabelNFDecidable c l
  exact inferInstance

def lowerGuardCaseValidNF (c : LowerGuardCase) : Prop :=
  c.before.1 ∈ lowerGuardStates ∧ c.before.2 ∈ lowerGuardStates ∧
  guardLabelsNF c ∧
  (c.run = true → lowerGuardSuffix c.before.1 [3,1] = false ∧
    lowerGuardSuffix c.before.2 [3,1] = false ∧
    lowerGuardSafe (c.before.1++[3,3]) = true ∧ lowerGuardSafe (c.before.2++[3,3]) = true)

def lowerGuardCaseValidNFDecidable (c : LowerGuardCase) : Decidable (lowerGuardCaseValidNF c) := by
  unfold lowerGuardCaseValidNF
  let d1 : Decidable (c.before.1 ∈ lowerGuardStates) := inferInstance
  let d2 : Decidable (c.before.2 ∈ lowerGuardStates) := inferInstance
  let d3 : Decidable (guardLabelsNF c) := guardLabelsNFDecidable c
  let d4 : Decidable (c.run = true → lowerGuardSuffix c.before.1 [3,1] = false ∧
    lowerGuardSuffix c.before.2 [3,1] = false ∧
    lowerGuardSafe (c.before.1++[3,3]) = true ∧ lowerGuardSafe (c.before.2++[3,3]) = true) := inferInstance
  exact @instDecidableAnd _ _ d1 (@instDecidableAnd _ _ d2 (@instDecidableAnd _ _ d3 d4))

theorem guardLabelsNF_iff (c : LowerGuardCase) :
    guardLabelsNF c ↔ ∀ l ∈ c.labels, (∀ d ∈ l.1++l.2, (d:ℕ) ≤ 3) ∧ (l.1 ≠ [] ∨ l.2 ≠ []) ∧
      lowerGuardSafe (c.before.1++l.1.reverse) = true ∧
      lowerGuardSafe (c.before.2++l.2) = true ∧ (∀ right : Bool, guardRight c l right) := by
  unfold guardLabelsNF
  rw [List.forall_iff_forall_mem]
  constructor
  · intro h l hl
    have hl' := h l hl
    rcases hl' with ⟨hd, hn, hs1, hs2, hr⟩
    exact ⟨hd, hn, hs1, hs2, (Bool.forall_bool).mpr hr⟩
  · intro h l hl
    have hl' := h l hl
    rcases hl' with ⟨hd, hn, hs1, hs2, hr⟩
    exact ⟨hd, hn, hs1, hs2, (Bool.forall_bool).mp hr⟩

theorem lowerGuardCaseValidNF_iff (c : LowerGuardCase) :
    lowerGuardCaseValidNF c ↔ lowerGuardCaseValid c := by
  unfold lowerGuardCaseValidNF lowerGuardCaseValid
  constructor
  · intro h
    rcases h with ⟨h1,h2,h3,h4⟩
    refine ⟨h1,h2,?_ ,h4⟩
    exact (guardLabelsNF_iff c).mp h3
  · intro h
    rcases h with ⟨h1,h2,h3,h4⟩
    refine ⟨h1,h2,?_ ,h4⟩
    exact (guardLabelsNF_iff c).mpr h3

def lowerGuardCaseValidDecidable (c : LowerGuardCase) : Decidable (lowerGuardCaseValid c) :=
  @decidable_of_iff (lowerGuardCaseValid c) (lowerGuardCaseValidNF c)
    (lowerGuardCaseValidNF_iff c) (lowerGuardCaseValidNFDecidable c)

def guardEqualPredDecidable (c : LowerGuardCase) :
    Decidable (c.mixed = false → lowerGuardCaseValid c) := by
  let d0 : Decidable (c.mixed = false) := inferInstance
  let d1 : Decidable (lowerGuardCaseValid c) := lowerGuardCaseValidDecidable c
  exact match d0, d1 with
    | isFalse h, _ => isTrue (fun hp => False.elim (h hp))
    | isTrue h, isTrue hp => isTrue (fun _ => hp)
    | isTrue h, isFalse hn => isFalse (fun f => hn (f h))

def guardEqualChunkDecidable (xs : List LowerGuardCase) :
    Decidable (∀ c ∈ xs, c.mixed = false → lowerGuardCaseValid c) :=
  @List.decidableBAll _ (fun c : LowerGuardCase => c.mixed = false → lowerGuardCaseValid c)
    (fun c => guardEqualPredDecidable c) xs

example : ∀ c ∈ (lowerGuardCases.take 25), c.mixed = false → lowerGuardCaseValid c := by
  exact @of_decide_eq_true _ (guardEqualChunkDecidable (lowerGuardCases.take 25)) rfl

theorem solution (hc : lowerGuardCatalogValid) :
    ∀ c ∈ lowerGuardCases, c.mixed = false → lowerGuardCaseValid c := by
  let d : Decidable (∀ c ∈ lowerGuardCases, c.mixed = false → lowerGuardCaseValid c) :=
    @List.decidableBAll _ (fun c : LowerGuardCase => c.mixed = false → lowerGuardCaseValid c)
      (fun c => guardEqualPredDecidable c) lowerGuardCases
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  exact @of_decide_eq_true _ d rfl
