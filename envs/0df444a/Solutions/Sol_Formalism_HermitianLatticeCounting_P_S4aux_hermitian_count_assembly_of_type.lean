-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_count_assembly_of_type
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.021832+00:00
-- url     : https://prove2.me/submissions/33ee2f68-086f-47b7-a75d-df0275ea38c8

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_type_cauchy_schwarz
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_assemblyNG2

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
theorem _root_.solution : AssemblyNG2 := Part2.assemblyNG2 type_cauchy_schwarz
end Formalism.HermitianLatticeCounting.P.S4aux
