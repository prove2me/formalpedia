-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.lagrangian_dual_convexity
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:29:25.480185+00:00
-- url     : https://prove2.me/submissions/59a40582-c3b6-4c23-9b12-a84a9060225e

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsEmbedOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.ConjugacyDualityD

namespace DualCvxCex

theorem top_exc : MExchangeAxiom (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) := by
  intro x hx
  exact absurd rfl hx

theorem empty_exc : ExchangeAxiomB (∅ : Set (Unit → ℤ)) := by
  intro x hx; exact absurd hx (Set.notMem_empty x)

theorem KR_top (y : Unit → ℤ) (x : Unit → ℤ) :
    KR (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) (fun _ => (0 : WithTop ℝ)) ∅ x y = ⊤ := by
  unfold KR
  apply sInf_eq_top.mpr
  rintro t ⟨u, rfl⟩
  simp [Fr, F0, ToEReal]
  rfl

theorem g_top (y : Unit → ℤ) :
    GRSmall (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) (fun _ => (0 : WithTop ℝ)) ∅ y = ⊤ := by
  unfold GRSmall
  apply sInf_eq_top.mpr
  rintro t ⟨x, rfl⟩
  exact KR_top y x

end DualCvxCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r),
    (IsNegOf (fun h => SBF h ∧ TRF h) (GRSmall c (fun _ => (0 : WithTop ℝ)) B) ∨
      ∀ y, GRSmall c (fun _ => (0 : WithTop ℝ)) B y = ⊥) ∧
    (IsNegOf L2Convex (GRSmall c r B) ∨ (∀ y, GRSmall c r B y = ⊥) ∨
      (∀ y, GRSmall c r B y = ⊤)) ∧
    (IsEmbedOf MExchangeAxiom (PhiR c (fun _ => (0 : WithTop ℝ)) B) ∨
      (∀ u, PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊤ ∨
        PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊥)) ∧
    (IsEmbedOf M2Convex (PhiR c r B) ∨ (∀ u, PhiR c r B u = ⊤ ∨ PhiR c r B u = ⊥))) := by
  intro h
  have H := (h (fun _ => ⊤) (fun _ => ⊤) ∅ DualCvxCex.empty_exc DualCvxCex.top_exc
    DualCvxCex.top_exc).1
  have hg := DualCvxCex.g_top (fun _ => 0)
  rcases H with ⟨k, -, hk⟩ | H
  · have := hk (fun _ => 0)
    rw [hg] at this
    have h2 : ToEReal (k (fun _ => 0)) = ⊥ := EReal.neg_eq_top_iff.mp this.symm
    exact WithBot.coe_ne_bot h2
  · have := H (fun _ => 0)
    rw [hg] at this
    exact absurd this (by decide)
