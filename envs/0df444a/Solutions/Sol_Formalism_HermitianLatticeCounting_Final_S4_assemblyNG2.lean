-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.assemblyNG2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.050943+00:00
-- url     : https://prove2.me/submissions/e1e245c6-d2bb-48f3-a6c6-017a35628373

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_count_assembly_of_type
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_count_assembly_of_type


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly_of_type
end Formalism.HermitianLatticeCounting.Final.S4
