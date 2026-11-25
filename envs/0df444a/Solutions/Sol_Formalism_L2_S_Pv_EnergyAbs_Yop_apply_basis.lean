-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Yop_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:50.822872+00:00
-- url     : https://prove2.me/submissions/754ff993-793c-41c8-b55d-200ed5bfe25a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Yop_apply

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
theorem _root_.solution (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G)
    (j : Fin (Module.finrank ℂ V)) :
    Yop μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) := by
  rw [Yop_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal]; simp
  · intro i _ hij
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal, if_neg hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h
end Formalism.L2.S.Pv.EnergyAbs
