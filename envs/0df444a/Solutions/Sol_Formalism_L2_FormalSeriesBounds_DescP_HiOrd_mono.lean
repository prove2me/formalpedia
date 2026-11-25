-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.HiOrd.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:10.009881+00:00
-- url     : https://prove2.me/submissions/9eba0552-1e2c-4483-81e9-b43d56c06f88

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
namespace HiOrd
theorem _root_.solution {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := fun μ hμ => h μ (lt_of_lt_of_le hμ hK)
end HiOrd
end Formalism.L2.FormalSeriesBounds.DescP
