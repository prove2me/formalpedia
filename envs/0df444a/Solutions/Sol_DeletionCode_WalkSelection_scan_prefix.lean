-- Prove2me | solution 1 for DeletionCode.WalkSelection.scan_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:59.446713+00:00
-- url     : https://prove2.me/submissions/4a709777-715d-4e4b-bcf6-7c05f1856e86

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_independent_insert
section
namespace DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
private theorem ScanState.skip {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hsigned : SignedMember step S (step i)) :
    ScanState step Good (n + 1) S := by
  refine ⟨fun r hr => by have := hs.before r hr; omega, hs.good, hs.independent, ?_⟩
  intro j hj
  by_cases hbefore : j.val < n
  · exact hs.covered j hbefore
  · have hji : j = i := Fin.ext (by omega)
    subst j
    obtain ⟨r, hr, heq⟩ := hsigned
    exact ⟨r, hr, by have := hs.before r hr; omega, heq⟩
private theorem ScanState.append {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hout : step i ∉ selectedSpan step S)
    (hgood : Good (insert i S)) : ScanState step Good (n + 1) (insert i S) := by
  refine ⟨?_, hgood, independent_insert hs.independent i hout, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with hri | hrS
    · subst r; omega
    · have := hs.before r hrS
      omega
  · intro j hj
    by_cases hbefore : j.val < n
    · obtain ⟨r, hr, hle, heq⟩ := hs.covered j hbefore
      exact ⟨r, Finset.mem_insert_of_mem hr, hle, heq⟩
    · have hji : j = i := Fin.ext (by omega)
      subst j
      exact ⟨i, Finset.mem_insert_self i S, le_rfl, Or.inl rfl⟩
end DeletionCode.WalkSelection
end

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (hgood : Good ∅) (n : ℕ) (hn : n ≤ m) :
    Stopped step Good ∨ ∃ S, ScanState step Good n S := by
  classical
  induction n with
  | zero =>
    right
    refine ⟨∅, ?_, hgood, ?_, ?_⟩
    · intro r hr
      simp at hr
    · simp
    · intro j hj
      omega
  | succ n ih =>
    rcases ih (by omega) with hstop | ⟨S, hs⟩
    · exact Or.inl hstop
    · let i : Fin m := ⟨n, by omega⟩
      by_cases hsigned : SignedMember step S (step i)
      · exact Or.inr ⟨S, hs.skip i rfl hsigned⟩
      · by_cases hspan : step i ∈ selectedSpan step S
        · exact Or.inl ⟨i, S, hs, hsigned, Or.inl hspan⟩
        · have hind := independent_insert hs.independent i hspan
          by_cases hnewgood : Good (insert i S)
          · exact Or.inr ⟨insert i S, hs.append i rfl hspan hnewgood⟩
          · exact Or.inl ⟨i, S, hs, hsigned, Or.inr ⟨hspan, hind, hnewgood⟩⟩
end DeletionCode.WalkSelection
