-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.oIso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:54.012866+00:00
-- url     : https://prove2.me/submissions/e31f8e7b-be4d-4cfb-9003-5dc853fc1d66

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_OIsoOf
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_basisCriterion_holds
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_presentationIso_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution (hR : QuadRoots)
    (p n' : ℕ) (hp : p.Prime) (hn : 0 < n') (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [IsDomain W₁]
    [IsDiscreteValuationRing W₁] [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [CommRing O₁]
    [IsDomain O₁] [IsDiscreteValuationRing O₁] [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂]
    (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂) (w₁ : O₁) (w₂ : O₂) (a₁ : Irreducible (p : W₁))
    (a₂ : Irreducible (p : W₂)) (b₁ : Nat.card (W₁ ⧸ Ideal.span {(p : W₁)}) = p ^ n')
    (b₂ : Nat.card (W₂ ⧸ Ideal.span {(p : W₂)}) = p ^ n') (c₁ : IsAdicComplete (Ideal.span {(p : W₁)}) W₁)
    (c₂ : IsAdicComplete (Ideal.span {(p : W₂)}) W₂) (d₁ : j₁.Finite) (d₂ : j₂.Finite)
    (e₁ : IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁) (e₂ : IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂)
    (f₁ : w₁ ^ 2 = (p : O₁)) (f₂ : w₂ ^ 2 = (p : O₂)) (g₁ : Irreducible w₁) (g₂ : Irreducible w₂)
    (h₁ : Nat.card (O₁ ⧸ Ideal.span {w₁}) = p ^ (2 * n')) (h₂ : Nat.card (O₂ ⧸ Ideal.span {w₂}) = p ^ (2 * n'))
    (φW : W₁ ≃+* W₂) : ∃ φO : O₁ ≃+* O₂, (∀ x, φO (j₁ x) = j₂ (φW x)) ∧ φO w₁ = w₂ := by
  obtain ⟨f0, f1, θ₁, θ₂, r₁, r₂, s₁, s₂⟩ :=
    hR p n' hp hn W₁ W₂ O₁ O₂ j₁ j₂ w₁ w₂ a₁ a₂ b₁ b₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ φW
  have B₁ := basisCriterion_holds p n' hp W₁ O₁ j₁ w₁ θ₁ a₁ b₁ d₁ f₁ g₁ h₁ s₁
  have B₂ := basisCriterion_holds p n' hp W₂ O₂ j₂ w₂ θ₂ a₂ b₂ d₂ f₂ g₂ h₂ s₂
  obtain ⟨φO, k1, k2, _⟩ := presentationIso_holds W₁ W₂ O₁ O₂ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 (p : W₁) φW r₁ r₂
    (by rw [f₁, map_natCast]) (by rw [f₂, map_natCast, map_natCast]) B₁ B₂
  exact ⟨φO, k1, k2⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
