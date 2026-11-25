-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.integrable_sq_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:02:13.196063+00:00
-- url     : https://prove2.me/submissions/33410353-bd22-4d37-956a-abe55a647641

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {u : ℂ → E} (hu : MemLp u 2 volume) : Integrable (fun z => ‖u z‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hu.1).1 hu
end Formalism.FourierDecayAlt.P.PBK
