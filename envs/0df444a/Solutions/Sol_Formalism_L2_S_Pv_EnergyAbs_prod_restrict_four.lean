-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.prod_restrict_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:27:53.05193+00:00
-- url     : https://prove2.me/submissions/2bfdabe3-a655-4c93-a5d3-cdedfd9a2419

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (A A' : Set G) :
    (ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')) =
      ((ν.prod μS).prod (ν'.prod μS')).restrict ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A')) := by
  have e1 : ν.prod (μS.restrict A) = (ν.prod μS).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have e2 : ν'.prod (μS'.restrict A') = (ν'.prod μS').restrict (Set.univ ×ˢ A') := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e1, e2, Measure.prod_restrict]
end Formalism.L2.S.Pv.EnergyAbs
