-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing.residueRingCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:16.443056+00:00
-- url     : https://prove2.me/submissions/4ab9183c-285e-40c0-8fa6-e311b3296adb

import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLattice
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_FlagKernelVanishing
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_residueRing_card_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing
namespace Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.ResidueRingCard := Formalism.HermitianLatticeCounting.P.residueRing_card_eq
end Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing
