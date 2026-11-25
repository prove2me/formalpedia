-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Yop_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:29.365061+00:00
-- url     : https://prove2.me/submissions/9f55afb9-f010-480f-893b-b1af98a44004

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) :
    Yop μS ν σ w W Ω e =
      ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
  simp only [Yop, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
end Formalism.L2.S.Pv.EnergyAbs
