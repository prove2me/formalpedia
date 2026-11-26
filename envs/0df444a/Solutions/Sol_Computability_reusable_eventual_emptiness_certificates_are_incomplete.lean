-- Prove2me | solution 1 for Computability.reusable_eventual_emptiness_certificates_are_incomplete
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T18:45:40.107836+00:00
-- url     : https://prove2.me/submissions/10f3e024-6692-47a8-bca9-fb95c4794e76

import Mathlib.Computability.Halting

set_option autoImplicit false

namespace PvsNP.ReusableEmptySlotBarrier

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The bounded program ignores its input bits and reports only whether the
specified computation produced an answer within its current fuel. -/
def boundedAccept (c : Code) (length : ℕ) : Bool :=
  (evaln length c 0).isSome

/-- The acceptor has an empty slice at every sufficiently late index. -/
def EventuallyEmpty (lengths : ℕ → ℕ) (c : Code) : Prop :=
  ∃ threshold, ∀ i ≥ threshold, boundedAccept c (lengths i) = false

theorem eventuallyEmpty_iff {lengths : ℕ → ℕ}
    (cofinal : ∀ threshold fuel : ℕ, ∃ i ≥ threshold, fuel ≤ lengths i)
    (c : Code) : EventuallyEmpty lengths c ↔ ¬ (eval c 0).Dom := by
  constructor
  · rintro ⟨threshold, empty⟩ halts
    obtain ⟨value, hasValue⟩ := Part.dom_iff_mem.mp halts
    obtain ⟨fuel, finds⟩ := evaln_complete.mp hasValue
    obtain ⟨i, late, enough⟩ := cofinal threshold fuel
    have findsLater := evaln_mono enough finds
    have rejects := empty i late
    have computation : evaln (lengths i) c 0 = some value := by simpa using findsLater
    simp [boundedAccept, computation] at rejects
  · intro diverges
    refine ⟨0, fun i _ => ?_⟩
    cases computation : evaln (lengths i) c 0 with
    | none => simp [boundedAccept, computation]
    | some value =>
      have finds : value ∈ evaln (lengths i) c 0 := by simp [computation]
      exact (diverges (Part.dom_iff_mem.mpr ⟨value, evaln_sound finds⟩)).elim

/-- A recursively enumerable bank can certify eventual emptiness soundly
for these length-based acceptors only if it misses some eventually empty one. -/
theorem some_empty_missing_from_reusable_bank {lengths : ℕ → ℕ}
    (cofinal : ∀ threshold fuel : ℕ, ∃ i ≥ threshold, fuel ≤ lengths i)
    {covered : Code → Prop} (enumerable : REPred covered)
    (sound : ∀ c, covered c → EventuallyEmpty lengths c) :
    ∃ c, EventuallyEmpty lengths c ∧ ¬ covered c := by
  classical
  by_contra! complete
  apply ComputablePred.halting_problem_not_re 0
  apply enumerable.of_eq
  intro c
  exact Iff.trans ⟨sound c, complete c⟩ (eventuallyEmpty_iff cofinal c)

/-- The hypothesis on lengths holds for each positive-period progression. -/
theorem some_empty_missing_on_progression (offset period : ℕ) (pos : 0 < period)
    {covered : Code → Prop} (enumerable : REPred covered)
    (sound : ∀ c, covered c → EventuallyEmpty (fun i => offset + period * i) c) :
    ∃ c, EventuallyEmpty (fun i => offset + period * i) c ∧ ¬ covered c := by
  apply some_empty_missing_from_reusable_bank _ enumerable sound
  intro threshold fuel
  refine ⟨threshold + fuel, Nat.le_add_right _ _, ?_⟩
  have positivePeriod : 1 ≤ period := pos
  have steps : threshold + fuel ≤ period * (threshold + fuel) := by
    simpa using Nat.mul_le_mul_right (threshold + fuel) positivePeriod
  omega

/-- No computable checker can prove eventual emptiness soundly and certify
every eventual-empty code. The certificate may encode a claimed starting
index or any other finite auxiliary information. -/
theorem some_empty_lacks_reusable_certificate (offset period : ℕ) (pos : 0 < period)
    (check : Code × ℕ → Bool) (computable : Computable check)
    (sound : ∀ c z, check (c,z) = true →
      EventuallyEmpty (fun i => offset + period * i) c) :
    ∃ c, EventuallyEmpty (fun i => offset + period * i) c ∧
      ∀ z, check (c,z) = false := by
  have search : Partrec (fun c : Code => Nat.rfind fun z => Part.some (check (c,z))) :=
    Partrec.rfind computable.partrec
  have enumerable : REPred (fun c : Code => ∃ z, check (c,z) = true) :=
    search.dom_re.of_eq fun c => by
      let test : ℕ →. Bool := fun z => Part.some (check (c,z))
      change (Nat.rfind test).Dom ↔ _
      refine Nat.rfind_dom.trans ?_
      constructor
      · rintro ⟨z, accepted, _⟩
        exact ⟨z, (Part.mem_some_iff.mp accepted).symm⟩
      · rintro ⟨z, accepted⟩
        refine ⟨z, Part.mem_some_iff.mpr accepted.symm, ?_⟩
        intro i before
        exact Part.some_dom _
  obtain ⟨c, empty, missing⟩ := some_empty_missing_on_progression offset period pos
    enumerable (fun c ⟨z, verified⟩ => sound c z verified)
  exact ⟨c, empty, fun z => Bool.eq_false_iff.mpr fun accepted => missing ⟨z, accepted⟩⟩

end PvsNP.ReusableEmptySlotBarrier

open Nat.Partrec (Code)

theorem solution (offset period : ℕ)
    (positive : 0 < period) (check : Code × ℕ → Bool) (computable : Computable check)
    (sound : ∀ c z, check (c,z) = true → ∃ threshold, ∀ i ≥ threshold,
      (Nat.Partrec.Code.evaln (offset + period * i) c 0).isSome = false) :
    ∃ c, (∃ threshold, ∀ i ≥ threshold,
      (Nat.Partrec.Code.evaln (offset + period * i) c 0).isSome = false) ∧
      ∀ z, check (c,z) = false := by
  exact PvsNP.ReusableEmptySlotBarrier.some_empty_lacks_reusable_certificate
    offset period positive check computable sound

#print axioms solution
