-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.layerCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:26:21.584855+00:00
-- url     : https://prove2.me/submissions/67ddeb26-60c1-4a14-9547-de59475bf14a

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_KappaConstantAssembly
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_layer_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
namespace Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.LayerCount := Formalism.HermitianLatticeCounting.P.layer_count
end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
