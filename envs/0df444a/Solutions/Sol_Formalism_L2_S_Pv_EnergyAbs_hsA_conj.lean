-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.hsA_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:33.565283+00:00
-- url     : https://prove2.me/submissions/9a6884c4-a344-46fd-bdca-dea56f1fc1e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_hsA_eq_adjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
section HS
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem norm_sq_apply_of_inner_preserving {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ) (v : E) : ‖U v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := hU v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h
end HS
section Rep
variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
end Rep
section Kernel
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
end Kernel
section Quot
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end Quot
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by
  have h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) =
      Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U')) := by
    unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact norm_sq_apply_of_inner_preserving U hU _
  rw [h1, hsA_eq_adjoint, hsA_eq_adjoint A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact norm_sq_apply_of_inner_preserving U' hU' _
end Formalism.L2.S.Pv.EnergyAbs
