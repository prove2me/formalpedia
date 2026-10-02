-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_and_mnat_domains
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:56:59.668526+00:00
-- url     : https://prove2.me/submissions/09ad50c1-e411-458f-be5b-3794c1e02cf7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatConvexSet

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsB in
theorem p2m_2d204c55_dom_of_mexc {W : Type*} [Fintype W] [DecidableEq W]
    (g : (W → ℤ) → WithTop ℝ) (h : MExchangeAxiom g) : ExchangeAxiomB (DomZ g) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hle⟩ := h x hx y hy u hu
  refine ⟨v, hv, ?_⟩
  have hsum : g x + g y ≠ ⊤ := WithTop.add_ne_top.2 ⟨hx, hy⟩
  have h2 := ne_top_of_le_ne_top hsum hle
  exact WithTop.add_ne_top.1 h2

open DiscreteConvex.MConvexFunctionsB in
theorem p2m_2d204c55_dom_lift {W : Type*} [Fintype W]
    (f : (W → ℤ) → WithTop ℝ) : DomZ (LiftedFunction f) = LiftedSet (DomZ f) := by
  ext x
  simp only [DomZ, LiftedFunction, LiftedSet, Set.mem_ofPred_eq]
  split_ifs with hc
  · exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · simp [hc]

open DiscreteConvex.MConvexFunctionsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → ExchangeAxiomB (DomZ f)) ∧
    (MNaturalConvex f → MNatConvexSet (DomZ f)) := by
  refine ⟨p2m_2d204c55_dom_of_mexc f, fun h => ?_⟩
  unfold MNatConvexSet
  rw [← p2m_2d204c55_dom_lift]
  exact p2m_2d204c55_dom_of_mexc _ h

