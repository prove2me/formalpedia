-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_dil_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:56.143954+00:00
-- url     : https://prove2.me/submissions/0bdb630b-d831-4b03-96aa-1a39b378af2e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_dil

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
theorem _root_.solution (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) :
    Tendsto (fun ρ : ℂ => ∫ z, (‖ρ‖ * ab (ρ * z) - ab z) ^ 2) (𝓝 1) (𝓝 0) := by
  have h := tendsto_dil ab hab 1 one_ne_zero
  refine h.congr fun ρ => ?_
  congr 1
  funext z
  rw [Real.norm_eq_abs, sq_abs, norm_one, one_smul, one_mul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.PBK
