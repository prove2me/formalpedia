-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.assemblyNG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:20.792811+00:00
-- url     : https://prove2.me/submissions/b1fcf565-19b8-4ede-b7eb-5c35a6e78aef

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_count_assembly
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_count_assembly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4
namespace Formalism.HermitianLatticeCounting.Final.S4
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.AssemblyNG := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly
end Formalism.HermitianLatticeCounting.Final.S4
