-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:19.873704+00:00
-- url     : https://prove2.me/submissions/e4a1db72-73aa-43a4-bc17-0c3051762da1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {X Q₁ Q₂ : Type} (π₁ : X → Q₁) (π₂ : X → Q₂) (s₁ : Q₁ → X) (s₂ : Q₂ → X)
    (h₁ : ∀ q, π₁ (s₁ q) = q) (h₂ : ∀ q, π₂ (s₂ q) = q)
    (hk : ∀ x x', π₁ x = π₁ x' ↔ π₂ x = π₂ x') (f : X → ℂ)
    (hf : ∀ x x', π₁ x = π₁ x' → f x = f x') : ∑ᶠ q, f (s₁ q) = ∑ᶠ q, f (s₂ q) := by
  refine finsum_eq_of_bijective (fun q => π₂ (s₁ q)) ⟨?_, ?_⟩ ?_
  · intro q q' h
    have := (hk _ _).2 h
    rwa [h₁, h₁] at this
  · intro q
    refine ⟨π₁ (s₂ q), ?_⟩
    show π₂ (s₁ (π₁ (s₂ q))) = q
    rw [(hk _ _).1 (h₁ (π₁ (s₂ q))), h₂]
  · intro q
    exact hf _ _ ((hk _ _).2 (h₂ _).symm)
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
