-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.it_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:15.11722+00:00
-- url     : https://prove2.me/submissions/03e0751b-a9b1-47eb-9c63-84a783b3fbfb

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
theorem _root_.solution (D : PS R n d → PS R n d) (B : PS R n d) (hD : ∀ A, D (A * B) = D A * B) :
    ∀ (N : ℕ) (A : PS R n d), D^[N] (A * B) = D^[N] A * B
  | 0, _ => rfl
  | N + 1, A => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hD, solution D B hD N]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
