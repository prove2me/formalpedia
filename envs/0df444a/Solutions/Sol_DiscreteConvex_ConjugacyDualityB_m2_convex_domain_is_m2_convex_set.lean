-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.m2_convex_domain_is_m2_convex_set
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:39:21.79502+00:00
-- url     : https://prove2.me/submissions/04f780e1-cd41-4e30-8a06-2a48416bd398

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

set_option autoImplicit false

open DiscreteConvex.ConjugacyDualityB

namespace M2Dom

/-- The effective domain of an M-convex function is an M-convex set. -/
theorem dom_exc {W : Type*} [Fintype W] [DecidableEq W] (f : (W → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) : ExchangeAxiomB (DomZ f) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hineq⟩ := hf x hx y hy u hu
  have hfin : f x + f y ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hx, hy⟩
  have hfin' := ne_top_of_le_ne_top hfin hineq
  exact ⟨v, hv, (WithTop.add_ne_top.mp hfin').1, (WithTop.add_ne_top.mp hfin').2⟩

theorem dom_add {W : Type*} [Fintype W] [DecidableEq W] (f1 f2 : (W → ℤ) → WithTop ℝ) :
    DomZ (fun x => f1 x + f2 x) = DomZ f1 ∩ DomZ f2 := by
  ext x
  simp only [DomZ, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact WithTop.add_ne_top

theorem lifted_dom {W : Type*} [Fintype W] [DecidableEq W] (f : (W → ℤ) → WithTop ℝ) :
    LiftedSet (DomZ f) = DomZ (LiftedFunction f) := by
  ext x
  simp only [LiftedSet, DomZ, LiftedFunction, Set.mem_ofPred_eq]
  by_cases h : x none = -(∑ v : W, x (some v))
  · simp [h]
  · simp [h]

end M2Dom

open M2Dom in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → M2ConvexSet (DomZ f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → MNat2ConvexSet (DomZ f)) := by
  constructor
  · rintro f ⟨f1, f2, h1, h2, rfl⟩
    exact ⟨DomZ f1, DomZ f2, dom_exc f1 h1, dom_exc f2 h2, dom_add f1 f2⟩
  · rintro f ⟨f1, f2, h1, h2, rfl⟩
    refine ⟨DomZ f1, DomZ f2, ?_, ?_, dom_add f1 f2⟩
    · show ExchangeAxiomB (LiftedSet (DomZ f1))
      rw [lifted_dom]; exact dom_exc _ h1
    · show ExchangeAxiomB (LiftedSet (DomZ f2))
      rw [lifted_dom]; exact dom_exc _ h2

#print axioms solution
