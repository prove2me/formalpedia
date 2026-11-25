-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.inner_integral_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:59.692681+00:00
-- url     : https://prove2.me/submissions/19205130-8ec8-42c9-bbb3-fa9cb4bd1460

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {α : Type*} [MeasurableSpace α] {m : Measure α} {f : α → HH} (hf : Integrable f m)
    (v : HH) : ⟪∫ x, f x ∂m, v⟫_ℂ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by
  have h : ∫ x, ⟪v, f x⟫_ℂ ∂m = ⟪v, ∫ x, f x ∂m⟫_ℂ := integral_inner hf v
  calc ⟪∫ x, f x ∂m, v⟫_ℂ = conj ⟪v, ∫ x, f x ∂m⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∫ x, ⟪v, f x⟫_ℂ ∂m) := by rw [h]
    _ = ∫ x, conj ⟪v, f x⟫_ℂ ∂m := integral_conj.symm
    _ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by simp_rw [inner_conj_symm]
end Formalism.L2.S.Pv.EnergyAbs
