-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.sqrt_hsA_le_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:46.220605+00:00
-- url     : https://prove2.me/submissions/824d5fde-c3d6-4b5e-ab22-16ae2fd7b5b5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_hsC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by
  simp_rw [← norm_hsC]
  have h : hsC A = hsC B + hsC (A - B) := by
    simp [map_sub]
  rw [h]
  exact norm_add_le _ _
end Formalism.L2.S.Pv.EnergyAbs
