-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.continuous_rk1A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:03.699474+00:00
-- url     : https://prove2.me/submissions/5e524793-5feb-4021-9837-425302efe23d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_rankOne_eq_smulRightL

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
theorem _root_.solution {α : Type*} [TopologicalSpace α] {f : α → V} {g : α → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => rk1A (f x) (g x)) := by
  simp only [rankOne_eq_smulRightL]
  exact ((ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp
    ((innerSL ℂ).continuous.comp hg)).clm_apply hf
end Formalism.L2.S.Pv.EnergyAbs
