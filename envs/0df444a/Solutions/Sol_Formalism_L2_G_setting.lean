-- Prove2me | solution 1 for Formalism.L2.G.setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:56.285152+00:00
-- url     : https://prove2.me/submissions/5e361e85-f4b9-4c60-a3dd-4dba45b1be22

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
import Theorems.Thm_Formalism_L2_G_settingStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.L2.G
theorem _root_.solution (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) :=
  (settingStd p n h5 h2 he).1
end Formalism.L2.G
