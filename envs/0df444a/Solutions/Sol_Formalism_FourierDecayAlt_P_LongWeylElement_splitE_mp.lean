-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.splitE_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:06.764485+00:00
-- url     : https://prove2.me/submissions/b30e919b-eaf2-4384-ba65-3d53f26728e1

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
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (r' : ℕ) : MeasurePreserving (splitE r') volume volume := by
  first
    | exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).comp
        (MeasurePreserving.symm _ (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))))
    | exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).comp
        ((MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))).symm _)
end Formalism.FourierDecayAlt.P.LongWeylElement
