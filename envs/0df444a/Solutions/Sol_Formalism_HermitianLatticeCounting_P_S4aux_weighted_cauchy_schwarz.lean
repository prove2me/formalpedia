-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.weighted_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:27.545367+00:00
-- url     : https://prove2.me/submissions/e4605123-dd19-47fc-9a2d-1373c8cd7c4c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : WeightedCS := by
  intro ι _ V _ v W hW
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le)
        (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)
      have := (hW i).ne'
      apply le_of_eq
      field_simp
end Formalism.HermitianLatticeCounting.P.S4aux
