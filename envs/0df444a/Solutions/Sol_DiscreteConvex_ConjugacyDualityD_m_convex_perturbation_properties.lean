-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.m_convex_perturbation_properties
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:24:43.168882+00:00
-- url     : https://prove2.me/submissions/3a2b7765-5976-4ba5-bd74-1ecca7ae3ce4

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_F0
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.ConjugacyDualityD

namespace PertCex

/-- The indicator of `{0} ⊆ ℤ^Unit`. -/
noncomputable def r (u : Unit → ℤ) : WithTop ℝ := if u () = 0 then 0 else ⊤

theorem r_exc : MExchangeAxiom r := by
  intro x hx y hy u hu
  exfalso
  have h1 : x () = 0 := by by_contra h; exact hx (by simp [r, h])
  have h2 : y () = 0 := by by_contra h; exact hy (by simp [r, h])
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  have : u = () := rfl
  subst this
  omega

theorem r_int : IsIntegerValuedFn r := by
  intro x; unfold r; split_ifs
  · right; exact ⟨0, by simp⟩
  · left; rfl

theorem c_int : IsIntegerValuedFn (fun _ : Unit → ℤ => (0 : WithTop ℝ)) :=
  fun _ => Or.inr ⟨0, by simp⟩

theorem empty_exc : ExchangeAxiomB (∅ : Set (Unit → ℤ)) := by
  intro x hx; exact absurd hx (Set.notMem_empty x)

end PertCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hr : MExchangeAxiom r) (hr0 : r (fun _ => (0 : ℤ)) = 0),
    (∀ x, Fr c r B x (fun _ => 0) = c x) ∧
    (∀ x, MExchangeAxiom (F0 c B x) ∨ ∀ u, F0 c B x u = ⊤) ∧
    (∀ x, M2Convex (Fr c r B x) ∨ ∀ u, Fr c r B x u = ⊤) ∧
    (∀ x, ConvexConjE (ConvexConjE (fun u => ToEReal (Fr c r B x u))) =
      fun u => ToEReal (Fr c r B x u)) ∧
    (∀ x u, ToEReal (Fr c r B x u) =
      sSup {t : EReal | ∃ y, t = KR c r B x y - ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}) ∧
    (MExchangeAxiom c →
      ∀ u, M2Convex (fun x => Fr c r B x u) ∨ ∀ x, Fr c r B x u = ⊤)) := by
  intro h
  have H := (h (fun _ => 0) PertCex.r ∅ PertCex.c_int PertCex.r_int PertCex.empty_exc
    PertCex.r_exc (by simp [PertCex.r])).1 (fun _ => 0)
  simp [Fr, F0, IndicatorWT, PertCex.r] at H

#print axioms solution
