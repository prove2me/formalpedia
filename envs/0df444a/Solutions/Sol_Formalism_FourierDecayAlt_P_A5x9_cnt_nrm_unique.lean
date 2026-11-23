-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.cnt_nrm_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:00.010082+00:00
-- url     : https://prove2.me/submissions/27221a54-1a9b-4a2d-a814-2f7ec64e0e20

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ : Matrix (Fin n) (Fin n) K)
    (D₁ D₂ : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) (h₁ : Nrm R k Z₀ D₁)
    (h₂ : Nrm R k Z₀ D₂)
    (h : ∀ (x : Fin n → R) (j : Fin n), ((D₁.1 - D₂.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R) : D₁ = D₂ := by
  unfold Nrm at h₁ h₂
  rw [← h₁, ← h₂]
  congr 1
  exact Quotient.sound (s := dRel R k Z₀) h
end Formalism.FourierDecayAlt.P.A5x9
