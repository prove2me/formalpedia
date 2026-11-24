-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.class_number_squares
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:23.917387+00:00
-- url     : https://prove2.me/submissions/90fb3837-1f7a-4d8e-9fca-1e31599b8221

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_norm_sq_c
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : ClassSquares := by
  intro ι _ s _ _ _ V _ _ v
  push_cast
  have h1 : ∀ c : Quotient s, ((‖∑ i ∈ univ.filter (fun i => Quotient.mk s i = c), v i‖ : ℂ)) ^ 2
      = ∑ i ∈ univ.filter (fun i => Quotient.mk s i = c),
          ∑ j, if s.r i j then inner ℂ (v i) (v j) else 0 := by
    intro c
    rw [norm_sq_c, sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi' := (Finset.mem_filter.1 hi).2
    have : (Quotient.mk s j = c) ↔ s.r i j := by
      rw [← hi', Quotient.eq]; exact ⟨fun h => s.symm h, fun h => s.symm h⟩
    simp only [this]
  simp_rw [h1]
  rw [Finset.sum_fiberwise]
end Formalism.HermitianLatticeCounting.P.S4aux
