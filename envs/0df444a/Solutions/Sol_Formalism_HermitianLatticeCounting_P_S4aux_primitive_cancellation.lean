-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.primitive_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:23.798606+00:00
-- url     : https://prove2.me/submissions/d1b61168-e911-4058-83a9-55d5b7e6a294

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
theorem _root_.solution : PrimCancel := by
  intro E _ O th ka n c d hd h1 hk
  choose t ht hkt using hk
  refine ⟨∑ i, d i * t i, O.sum_mem fun i _ => O.mul_mem (hd i) (ht i), ?_⟩
  calc ka = ka * ∑ i, d i * c i := by rw [h1, mul_one]
    _ = ∑ i, d i * (ka * c i) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hkt i]; ring
end Formalism.HermitianLatticeCounting.P.S4aux
