-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.l2_convex_domain_is_l2_convex_set
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:22:19.918102+00:00
-- url     : https://prove2.me/submissions/79ec1325-83e9-4a5e-8775-d25473fe5194

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet

set_option autoImplicit false

section Helpersc4
open DiscreteConvex.ConjugacyDualityC
open scoped Pointwise

/-- The constant `+∞` function on `ℤ^Unit` is L2-convex (as `⊤ □ ⊤`) but has empty domain. -/
theorem top_l2convex_c4 : L2Convex (V := Unit) (fun _ => (⊤ : WithTop ℝ)) := by
  refine ⟨fun _ => ⊤, fun _ => ⊤, ⟨fun p q => by simp, ⟨0, fun p => by simp⟩⟩,
    ⟨fun p q => by simp, ⟨0, fun p => by simp⟩⟩, fun p => ?_, ?_⟩
  · unfold InfConvE
    have hs : {L : EReal | ∃ p1 p2 : Unit → ℤ, p = p1 + p2 ∧
        L = ToEReal (⊤ : WithTop ℝ) + ToEReal (⊤ : WithTop ℝ)} = {⊤} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨p1, p2, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨p, 0, by simp, rfl⟩
    rw [hs, sInf_singleton]
    exact top_ne_bot
  · funext p
    unfold InfConv
    have hs : {L : WithTop ℝ | ∃ p1 p2 : Unit → ℤ, p = p1 + p2 ∧
        L = (⊤ : WithTop ℝ) + (⊤ : WithTop ℝ)} = {⊤} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨p1, p2, -, rfl⟩
        simp
      · rintro rfl
        exact ⟨p, 0, by simp, by simp⟩
    rw [hs, csInf_singleton]

theorem not_l2convexset_dom_top_c4 :
    ¬ L2ConvexSet (DomZ (V := Unit) (fun _ => (⊤ : WithTop ℝ))) := by
  rintro ⟨D1, D2, h1, h2, hD⟩
  obtain ⟨p1, hp1⟩ := h1.1
  obtain ⟨p2, hp2⟩ := h2.1
  have hmem : p1 + p2 ∈ D1 + D2 := Set.add_mem_add hp1 hp2
  rw [← hD] at hmem
  exact hmem rfl

end Helpersc4

open DiscreteConvex.ConjugacyDualityC in
open Classical in
open scoped Pointwise in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → L2ConvexSet (DomZ g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → LNat2ConvexSet (DomZ g))) := by
  intro h
  exact not_l2convexset_dom_top_c4 ((h (V := Unit)).1 _ top_l2convex_c4)
