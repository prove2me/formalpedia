-- Prove2me | solution 1 for DeletionCode.WalkSelection.ScanState.generating_after_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:04.408817+00:00
-- url     : https://prove2.me/submissions/bda6a2e7-42b1-49c7-b84b-809729ab229d

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_independent_insert
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating
section
namespace DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
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
namespace ScanState
theorem _root_.solution {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (i : Fin m) (hi : i.val = n) (hout : walkStep p i ∉ selectedSpan (walkStep p) S) :
    GeneratingSelected p (insert i S) := by
  have htrue : ScanState (walkStep p) (fun _ => True) n S :=
    ⟨hs.before, trivial, hs.independent, hs.covered⟩
  exact (htrue.append i hi hout trivial).generating hp
end ScanState
end DeletionCode.WalkSelection
