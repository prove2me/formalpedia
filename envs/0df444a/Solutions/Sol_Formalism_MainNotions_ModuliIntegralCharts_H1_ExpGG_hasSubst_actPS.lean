-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG.hasSubst_actPS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:45.832946+00:00
-- url     : https://prove2.me/submissions/e83ee4ed-e1b5-462d-a6fb-d95b1308ef97

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const_actPS

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
theorem _root_.solution (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) :=
  hasSubst_of_constantCoeff_zero (fun q => const_actPS c a q)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
