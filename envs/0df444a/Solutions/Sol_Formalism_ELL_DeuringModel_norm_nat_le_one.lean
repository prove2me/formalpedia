-- Prove2me | solution 1 for Formalism.ELL.DeuringModel.norm_nat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:03.022298+00:00
-- url     : https://prove2.me/submissions/fcc1ce1c-1306-41ce-930b-e1a5d68a3b8e

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.DeuringModel
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.DeuringModel
theorem _root_.solution (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
end Formalism.ELL.DeuringModel
