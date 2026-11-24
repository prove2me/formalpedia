-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.eval_single_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:38.863679+00:00
-- url     : https://prove2.me/submissions/902b663f-9251-4bf5-85a7-9aab81e56f45

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
theorem _root_.solution {n d : ℕ} (χ : Pt S n d) (g : PS S 1 d) : ev (n := n) ![χ] g = subst (fam1 χ) g := by
  unfold ev
  congr 1
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
