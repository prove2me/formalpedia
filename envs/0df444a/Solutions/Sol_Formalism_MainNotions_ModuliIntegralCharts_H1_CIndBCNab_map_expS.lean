-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:43.746684+00:00
-- url     : https://prove2.me/submissions/248e03f0-0687-41c0-9805-d3afb1f2f61b

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
variable [Algebra ℚ S] [Algebra ℚ S']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
theorem _root_.solution {n : ℕ} (g : PS S n d) (hg : constantCoeff g = 0) :
    map ψ (FB.expS S g) = FB.expS S' (map ψ g) := by
  simp only [FB.expS]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg), PowerSeries.map_exp]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
