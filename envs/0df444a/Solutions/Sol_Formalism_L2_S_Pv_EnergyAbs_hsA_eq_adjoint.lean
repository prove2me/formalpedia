-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.hsA_eq_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:54.75174+00:00
-- url     : https://prove2.me/submissions/563e5988-6857-4824-a6cd-ae3ae6cbc82d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
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
private theorem sum_norm_inner_stdBasis_sq_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (x : E) :
    ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  exact (stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x
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
theorem _root_.solution (A : V' →L[ℂ] V) :
    hsA A = ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  calc ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪stdOrthonormalBasis ℂ V j, A (stdOrthonormalBasis ℂ V' i)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
    _ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i,
          (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
end Formalism.L2.S.Pv.EnergyAbs
