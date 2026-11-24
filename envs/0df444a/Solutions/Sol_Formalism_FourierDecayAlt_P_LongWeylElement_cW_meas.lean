-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.cW_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:32.601103+00:00
-- url     : https://prove2.me/submissions/cf748d8a-5e0d-4f13-a73e-7aa1861b88bb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r : ℕ) : Measurable fun c : Fin r → ℂ => ENNReal.ofReal (cWeight k r c) := by
  first
    | (unfold cWeight; fun_prop)
    | exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).norm).pow_const _)
    | (unfold cWeight; measurability)
end Formalism.FourierDecayAlt.P.LongWeylElement
