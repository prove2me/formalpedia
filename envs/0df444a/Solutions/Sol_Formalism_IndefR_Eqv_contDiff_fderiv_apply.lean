-- Prove2me | solution 1 for Formalism.IndefR.Eqv.contDiff_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:37.78113+00:00
-- url     : https://prove2.me/submissions/56743468-eb3f-4ba0-9ee6-19e04cb002b2

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (w : V) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
  (ContinuousLinearMap.apply ℝ ℂ w).contDiff.comp (hφ.fderiv_right (m := ∞) (by simp))
end Formalism.IndefR.Eqv
