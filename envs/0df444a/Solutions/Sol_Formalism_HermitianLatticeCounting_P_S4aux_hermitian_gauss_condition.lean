-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_gauss_condition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.215994+00:00
-- url     : https://prove2.me/submissions/94d15a68-1f2d-49a5-af2a-f25ad6086d25

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_gauss_sum_ring
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_hermGaussCond
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_annihilator_size

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
theorem _root_.solution : HermGaussCond := Part2.hermGaussCond hermitian_gauss_sum_ring annihilator_size
end Formalism.HermitianLatticeCounting.P.S4aux
