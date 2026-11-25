-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.memLp_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:23.469165+00:00
-- url     : https://prove2.me/submissions/ae9c2dc4-6652-4dce-8453-e0d27bc7145e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_map_mulEquiv

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
theorem _root_.solution {p : ENNReal} {f : ℂ → E} (hf : MemLp f p volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => f (ρ * z)) p volume := by
  have h1 : MemLp f p (Measure.map (mulEquiv ρ hρ) volume) := by
    rw [map_mulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (mulEquiv ρ hρ).measurable.aemeasurable
end Formalism.FourierDecayAlt.P.PBK
