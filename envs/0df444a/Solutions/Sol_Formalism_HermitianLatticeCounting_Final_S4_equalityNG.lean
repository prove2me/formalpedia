-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.equalityNG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:12.659434+00:00
-- url     : https://prove2.me/submissions/b73f8dbe-fcfb-46ad-a614-5d60846b3d37

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_count_equality
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_count_equality


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.EqualityNG := Formalism.HermitianLatticeCounting.P.hermitian_count_equality
end Formalism.HermitianLatticeCounting.Final.S4
