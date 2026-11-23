-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:58.061124+00:00
-- url     : https://prove2.me/submissions/6da4eb61-0c49-4829-b550-1539736e49ca

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_liftE_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_down

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable {M₁ M₂ C₁ C₂ : Type} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] {γ : Kˣ}
  {Φ₁ : M₁ →ₗ[R] K} {π₁ : M₁ →ₗ[R] C₁} {g₁ : M₁} {lam₁ : C₁ →ₗ[R] KR R}
  {Φ₂ : M₂ →ₗ[R] K} {π₂ : M₂ →ₗ[R] C₂} {g₂ : M₂} {lam₂ : C₂ →ₗ[R] KR R}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (f₁ : M₁) (f₂ : M₂) (hf : Φ₁ f₁ = Φ₂ f₂) :
    Nat.card {φ : C₁ ≃ₗ[R] C₂ // (∀ y, lam₂ (φ y) = lam₁ y) ∧ φ (π₁ f₁) = π₂ f₂} =
      Nat.card {Ψ : M₁ ≃ₗ[R] M₂ // (∀ x, Φ₂ (Ψ x) = Φ₁ x) ∧ Ψ g₁ = g₂ ∧ Ψ f₁ = f₂} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun φ => ⟨iso_liftE D₂ D₁ φ.1 φ.2.1, fun x => (iso_liftE_spec D₂ D₁ φ.1 φ.2.1 x).2, ?_, ?_⟩)
    ⟨?_, ?_⟩)
  · apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).1, D₁.pg, D₂.pg, map_zero]
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).2, D₁.Pg, D₂.Pg]
  · apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).1, φ.2.2]
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).2, hf]
  · intro φ φ' h
    apply Subtype.ext
    ext y
    obtain ⟨x, rfl⟩ := D₁.surj y
    have h1 : iso_liftE D₂ D₁ φ.1 φ.2.1 = iso_liftE D₂ D₁ φ'.1 φ'.2.1 := congrArg Subtype.val h
    rw [← (iso_liftE_spec D₂ D₁ φ.1 φ.2.1 x).1, ← (iso_liftE_spec D₂ D₁ φ'.1 φ'.2.1 x).1, h1]
  · rintro ⟨Ψ, hΨ, hg, hff⟩
    obtain ⟨φ, hφ⟩ := iso_down D₂ D₁ Ψ hg
    have hl : ∀ y, lam₂ (φ y) = lam₁ y := by
      intro y
      obtain ⟨x, rfl⟩ := D₁.surj y
      rw [hφ, D₂.lam_pi, D₁.lam_pi, hΨ]
    refine ⟨⟨φ, hl, by rw [hφ, hff]⟩, ?_⟩
    apply Subtype.ext
    ext x
    apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ hl x).1, hφ]
    · rw [(iso_liftE_spec D₂ D₁ φ hl x).2, hΨ]
end Formalism.FourierDecayAlt.P.A5x8
