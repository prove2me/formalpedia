-- Prove2me | solution 1 for ErdosPosa.exists_minCyc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:50.84186+00:00
-- url     : https://prove2.me/submissions/3e18731f-9d07-4077-ae9c-8c91a7f6a12f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] {H : SimpleGraph V} {S : Set V} (h : Cyc H S) :
    ∃ T ⊆ S, MinCyc H T := by
  induction hn : S.ncard using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hmin : ∀ T' ⊆ S, Cyc H T' → T' = S
    · exact ⟨S, subset_rfl, h, hmin⟩
    push Not at hmin
    obtain ⟨T', hT'S, hT', hne⟩ := hmin
    have hlt : T'.ncard < S.ncard :=
      Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2 ⟨hT'S, hne⟩) (Set.toFinite S)
    obtain ⟨T, hTT', hT⟩ := ih _ (hn ▸ hlt) hT' rfl
    exact ⟨T, hTT'.trans hT'S, hT⟩
end ErdosPosa
