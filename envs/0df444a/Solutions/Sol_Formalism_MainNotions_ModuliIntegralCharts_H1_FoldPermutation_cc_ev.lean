-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.cc_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:20.808032+00:00
-- url     : https://prove2.me/submissions/f56b52b0-0c8f-4d79-92d5-7cfdcef27474

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add


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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : LogPf.CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [e1]
  rw [LogPf.ev_add ha, LogPf.ev_C ha, map_add, LogPf.constantCoeff_ev ha h0, add_zero, constantCoeff_C]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
