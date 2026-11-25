-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.sqrt_hsA_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:42.631591+00:00
-- url     : https://prove2.me/submissions/6a9408f8-920f-45d3-a2bb-c8b5a5160c40

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
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → (V' →L[ℂ] V))
    (hf : Integrable f μ) :
    Real.sqrt (hsA (∫ x, f x ∂μ)) ≤ ∫ x, Real.sqrt (hsA (f x)) ∂μ := by
  simp_rw [← norm_hsC]
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact norm_integral_le_integral_norm _
end Formalism.L2.S.Pv.EnergyAbs
