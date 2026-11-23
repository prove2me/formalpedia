-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.cnt_nrm_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:59.354626+00:00
-- url     : https://prove2.me/submissions/54af3960-df81-4f8c-8c2c-6892fb69c8a1

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
    (D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) :
    ∃ D' : {D : Matrix (Fin n) (Fin n) K // IsD R k D}, Nrm R k Z₀ D' ∧
      ∀ (x : Fin n → R) (j : Fin n), ((D'.1 - D.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R := by
  refine ⟨Quotient.out (Quotient.mk (dRel R k Z₀) D), ?_, ?_⟩
  · unfold Nrm; rw [Quotient.out_eq]
  · exact Quotient.exact (Quotient.out_eq (Quotient.mk (dRel R k Z₀) D))
end Formalism.FourierDecayAlt.P.A5x9
