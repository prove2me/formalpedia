-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.conjugation_continuous_on_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:29.479641+00:00
-- url     : https://prove2.me/submissions/a6766e7c-c942-4323-9f18-222c4eeed941

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : ContinuousOn (conj2 : Mt k r × Mt k r → Mt k r) {p | detF p.1 ≠ 0} := by
  unfold conj2
  refine mulM_cont.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
  · exact (mulM_cont.comp (continuous_fst.prodMk continuous_snd)).continuousOn
  · exact invM_contOn.comp continuous_fst.continuousOn (fun p hp => hp)
end Formalism.FourierDecayAlt.P.B2x1
