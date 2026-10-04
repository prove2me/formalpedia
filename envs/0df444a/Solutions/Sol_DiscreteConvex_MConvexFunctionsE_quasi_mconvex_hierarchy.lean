-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.quasi_mconvex_hierarchy
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:06:49.942465+00:00
-- url     : https://prove2.me/submissions/9fe4d8fe-a528-4619-86b9-e848a185a1ce

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsE

namespace HierarchyCex

/-- Indicator of the single point `0 ∈ ℤ^Unit`. -/
noncomputable def ind : (Unit → ℤ) → WithTop ℝ :=
  fun x => if x () = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem mem_dom {x : Unit → ℤ} (hx : x ∈ DomZ ind) : x () = 0 := by
  by_contra h
  exact hx (by simp [ind, h])

theorem exc : MExchangeAxiom ind := by
  intro x hx y hy u hu
  exfalso
  have h1 := mem_dom hx
  have h2 := mem_dom hy
  simp only [SuppPos, Finset.mem_filter] at hu
  have : u = () := rfl
  subst this
  omega

theorem not_excw : ¬ MExchangeAxiomW ind := by
  rintro ⟨x, hx, y, hy, hne, -⟩
  apply hne
  funext i
  cases i
  rw [mem_dom hx, mem_dom hy]

end HierarchyCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ),
    (MExchangeAxiom f → SSQM f) ∧
    (SSQM f → QM f) ∧
    (MExchangeAxiomW f → SSQMw f) ∧
    (SSQMw f → QMw f) ∧
    (MExchangeAxiom f ↔ MExchangeAxiomW f) ∧
    (SSQM f → SSQMw f) ∧
    (QM f → QMw f) ∧
    (MExchangeAxiom f ↔ ∀ p : V → ℝ, QMw (LinearWeight f p))) := by
  intro h
  exact HierarchyCex.not_excw ((h HierarchyCex.ind).2.2.2.2.1.mp HierarchyCex.exc)

#print axioms solution
