-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:44.39841+00:00
-- url     : https://prove2.me/submissions/1b2e4129-ffb5-46fd-ba89-53b3af1ad104

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
theorem _root_.solution {σ : Type} (i : σ) (f : MvPowerSeries σ S) :
    map ψ (pderiv S i f) = pderiv S' i (map ψ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
