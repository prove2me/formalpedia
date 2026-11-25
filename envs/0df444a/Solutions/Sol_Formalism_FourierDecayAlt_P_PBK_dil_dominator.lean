-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.dil_dominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:14.153575+00:00
-- url     : https://prove2.me/submissions/e7f3fc06-2b12-48e2-895c-98c4fc1b31d8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_comp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_dil_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α : Type} {l : Filter α} (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) (lam : α → ℂ)
    (hlam : Tendsto lam l (𝓝 1)) :
    (∀ a D, ‖lam a‖ * ab (lam a * D) ≤ ab D + |‖lam a‖ * ab (lam a * D) - ab D|) ∧
    (∀ᶠ a in l, MemLp (fun D => |‖lam a‖ * ab (lam a * D) - ab D|) 2 volume) ∧
    Tendsto (fun a => ∫ D, |‖lam a‖ * ab (lam a * D) - ab D| ^ 2) l (𝓝 0) := by
  refine ⟨fun a D => by linarith [le_abs_self (‖lam a‖ * ab (lam a * D) - ab D)], ?_, ?_⟩
  · filter_upwards [hlam.eventually_ne one_ne_zero] with a ha
    exact (((memLp_comp_mul hab (lam a) ha).const_mul ‖lam a‖).sub hab).abs
  · have h := (tendsto_dil_real ab hab).comp hlam
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, sq_abs]
end Formalism.FourierDecayAlt.P.PBK
