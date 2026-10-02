-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_domain_is_lconvex_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:44:58.17271+00:00
-- url     : https://prove2.me/submissions/b15ee012-09f7-42e5-aa26-7c893e3c6628

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet

set_option autoImplicit false
universe u

open DiscreteConvex.LConvexFunctionsB in
lemma a133_part1 {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ)
    (hs : SBF g) (ht : TRF g) (hne : (DomZ g).Nonempty) : LConvexSet (DomZ g) := by
  refine ⟨hne, ?_, ?_⟩
  · intro p hp q hq
    have hp' : g p ≠ ⊤ := hp
    have hq' : g q ≠ ⊤ := hq
    have h := hs p q
    have hpq : g p + g q ≠ ⊤ := WithTop.add_ne_top.2 ⟨hp', hq'⟩
    have h2 : g (p ⊔ q) + g (p ⊓ q) ≠ ⊤ := ne_top_of_le_ne_top hpq h
    rw [WithTop.add_ne_top] at h2
    exact ⟨h2.1, h2.2⟩
  · obtain ⟨r, hr⟩ := ht
    intro p hp
    have hp' : g p ≠ ⊤ := hp
    constructor
    · show g (fun v => p v + 1) ≠ ⊤
      have e : (fun v => p v + 1) = p + 1 := rfl
      rw [e, hr p]
      exact WithTop.add_ne_top.2 ⟨hp', WithTop.coe_ne_top⟩
    · show g (fun v => p v - 1) ≠ ⊤
      intro htop
      have h1 := hr (fun v => p v - 1)
      have e : (fun v => p v - 1) + 1 = p := by funext v; simp
      rw [e, htop, WithTop.top_add] at h1
      exact hp' h1

open DiscreteConvex.LConvexFunctionsB in
theorem solution {V : Type u} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) :
    ((SBF g ∧ TRF g) → (DomZ g).Nonempty → LConvexSet (DomZ g)) ∧
    (LNaturalConvex g → (DomZ g).Nonempty → LNatConvexSet (DomZ g)) := by
  refine ⟨fun h hne => a133_part1 g h.1 h.2 hne, ?_⟩
  rintro ⟨hs, ht⟩ hne
  have key : LiftedSetL (DomZ g) = DomZ (LiftedFunctionL g) := rfl
  unfold LNatConvexSet
  rw [key]
  apply a133_part1 _ hs ht
  obtain ⟨p, hp⟩ := hne
  refine ⟨fun o => o.elim 0 p, ?_⟩
  have hp' : g p ≠ ⊤ := hp
  show g (fun v => p v - 0) ≠ ⊤
  simpa using hp'
