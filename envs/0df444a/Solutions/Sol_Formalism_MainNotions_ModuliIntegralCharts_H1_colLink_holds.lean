-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.colLink_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:57.999302+00:00
-- url     : https://prove2.me/submissions/692cdf19-c218-4a29-a9d5-9f386ad974de

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : ColLinkSt := by
  intro E _ _ _ H Dw n m b
  ext ℓ
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1
