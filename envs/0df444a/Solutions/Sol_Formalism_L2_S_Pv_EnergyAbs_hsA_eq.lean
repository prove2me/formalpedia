-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.hsA_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:49.700004+00:00
-- url     : https://prove2.me/submissions/1d4ac536-ec3a-4842-b84b-1b4096d04535

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem norm_sq_eq_sum_norm_inner_stdBasis_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, v⟫_ℂ‖ ^ 2 := by
  exact ((stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right v).symm
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (A : V' →L[ℂ] V) :
    hsA A = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V i, A (stdOrthonormalBasis ℂ V' j)⟫_ℂ‖ ^ 2 := by
  show ∑ j, ‖A (stdOrthonormalBasis ℂ V' j)‖ ^ 2 = _
  exact Finset.sum_congr rfl fun j _ => norm_sq_eq_sum_norm_inner_stdBasis_sq _
end Formalism.L2.S.Pv.EnergyAbs
