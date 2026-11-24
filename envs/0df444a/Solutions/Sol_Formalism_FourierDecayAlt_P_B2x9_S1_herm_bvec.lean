-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:13:01.265355+00:00
-- url     : https://prove2.me/submissions/ff669e56-a982-4eca-8507-a9da61349005

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9 Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9.S1
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) : herm H (bvec q) (bvec p) = H p q := by
  rw [herm_bvec_right_eq_mulVec_apply]
  simp [bvec, mulVec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.P.B2x9.S1
