-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.ev_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:14:02.696476+00:00
-- url     : https://prove2.me/submissions/00402a5f-6d34-4920-bfb4-5f551bdf4c77

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
theorem _root_.solution {m : ℕ} (a : Fin m → Pt R n d) (h0 : ∀ q i, constantCoeff (a q i) = 0)
    (g : PS R m d) (hg : constantCoeff g = 0) : constantCoeff (ev a g) = 0 := by
  unfold ev
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  all_goals first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h0 p.1 p.2)
    | exact fun p => h0 p.1 p.2
    | exact hg
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
