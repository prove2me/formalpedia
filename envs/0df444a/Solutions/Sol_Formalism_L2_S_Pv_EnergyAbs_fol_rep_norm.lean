-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.fol_rep_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:36.667953+00:00
-- url     : https://prove2.me/submissions/7956a350-0303-4e8a-83da-378facffc63f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
section General
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
private theorem norm_eq_of_inner_self_eq_inner_self_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : E} (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    have h' := h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    exact_mod_cast h'
  nlinarith [norm_nonneg a, norm_nonneg b]
end General
section Main
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
end Main
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x : G) (a : HH) : ‖σ x a‖ = ‖a‖ := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  exact norm_eq_of_inner_self_eq_inner_self_lemma (hin x a a)
end Formalism.L2.S.Pv.EnergyAbs
