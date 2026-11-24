-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.dLin_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:28.494923+00:00
-- url     : https://prove2.me/submissions/2a2a99f6-771d-4dc6-85f4-d39805e0d31d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_pt


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution (ℓ ε : Pt S 1 d) (hℓ1 : dLin ℓ = 1) (hinv : IsInvPair ε ℓ) : dLin ε = 1 := by
  have h := dLin_comp1 ℓ ε hinv.1
  rw [hinv.2.2.2, dLin_pt, hℓ1, one_mul] at h
  exact h.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
