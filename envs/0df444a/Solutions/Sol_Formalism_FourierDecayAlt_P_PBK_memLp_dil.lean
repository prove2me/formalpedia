-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.memLp_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:30.897397+00:00
-- url     : https://prove2.me/submissions/001c7b23-395d-4285-a1cb-ee7c5a8d96c5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_comp_mul

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
theorem _root_.solution {f : ℂ → E} (hf : MemLp f 2 volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => ‖ρ‖ • f (ρ * z)) 2 volume :=
  (memLp_comp_mul hf ρ hρ).const_smul ‖ρ‖
end Formalism.FourierDecayAlt.P.PBK
