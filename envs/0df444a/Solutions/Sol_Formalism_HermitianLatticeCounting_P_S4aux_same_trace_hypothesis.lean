-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.same_trace_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:25.259776+00:00
-- url     : https://prove2.me/submissions/493fe542-63d0-4095-82b7-6203dbe0a705

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dual_capacity_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_sameTraceHyp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dual_capacity_variant

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
theorem _root_.solution : SameTraceHyp := Part2.sameTraceHyp dual_capacity_formula dual_capacity_variant
end Formalism.HermitianLatticeCounting.P.S4aux
