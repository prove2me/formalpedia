-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.ae_mem_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:34.770421+00:00
-- url     : https://prove2.me/submissions/28eaf5fe-1b84-4023-9069-cbe335e6fd1d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt

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
theorem _root_.solution {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS'] {S S' : Set G}
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S ∧ p.2.2 ∈ S' := by
  have hS : ∀ᵐ s ∂μS, s ∈ S := ae_iff.mpr h0
  have hS' : ∀ᵐ s ∂μS', s ∈ S' := ae_iff.mpr h0'
  have a1 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S :=
    quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_snd.ae hS)
  have a2 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.2.2 ∈ S' :=
    quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_snd.ae hS')
  exact a1.and a2
end Formalism.L2.S.Pv.EnergyAbs
