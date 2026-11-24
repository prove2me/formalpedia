-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.ordGE_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:59.807065+00:00
-- url     : https://prove2.me/submissions/d4965a0a-d772-483d-8f46-dbf5ed49f6e8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
variable {k : Type} [CommRing k] {σ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
theorem _root_.solution (r : ℕ) : OrdGE r (0 : MvPowerSeries σ k) := by
  intro e _
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
