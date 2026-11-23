-- Prove2me | solution 1 for Formalism.FX.rectRes_ftc_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:05.595745+00:00
-- url     : https://prove2.me/submissions/4e365f61-acf6-468a-9f82-5cc154cfdd71

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.FX
namespace Formalism.FX
theorem _root_.solution {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)
end Formalism.FX
