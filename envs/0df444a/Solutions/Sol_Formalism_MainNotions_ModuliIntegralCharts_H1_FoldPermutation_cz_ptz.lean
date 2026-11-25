-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.cz_ptz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:23.717747+00:00
-- url     : https://prove2.me/submissions/a14a7460-fc80-45d0-ae87-d765f6a52fa4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
variable {k : Type} [CommRing k] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
theorem _root_.solution {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
