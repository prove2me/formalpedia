-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.hermitian_form_base_vector_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:12.539872+00:00
-- url     : https://prove2.me/submissions/ec4ae5df-e582-434d-babf-d46f5062bc10

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Hpk_first
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
private lemma star_bvec' {m : ℕ} (p : Fin m) : star (bvec p) = bvec p := by
  ext j
  by_cases h : j = p
  · subst h; simp [bvec]
  · simp [bvec, Pi.single_apply, h]
private lemma herm_bvec_right_eq_mulVec_apply {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (p : Fin m) :
    herm H u (bvec p) = (H *ᵥ u) p := by
  unfold herm
  rw [star_bvec']
  simp [bvec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9.S1
namespace Formalism.FourierDecayAlt.P.B2x9.S2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x9.S2
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (e0 k r') = u (iL k r') := by
  rw [show e0 k r' = bvec (iF k r') from rfl, herm_bvec_right_eq_mulVec_apply]
  simp [mulVec, dotProduct, Hpk_first]
end Formalism.FourierDecayAlt.P.B2x9
