-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG.actPS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:19.470181+00:00
-- url     : https://prove2.me/submissions/eaad2159-5990-4f89-ac65-d6b40c305dde

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS

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
theorem _root_.solution (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    actPS (Dw := Dw) (S := S) c u q + actPS (Dw := Dw) (S := S) c v q = actPS (Dw := Dw) (S := S) c (u + v) q := by
  simp only [actPS, map_add, add_smul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
