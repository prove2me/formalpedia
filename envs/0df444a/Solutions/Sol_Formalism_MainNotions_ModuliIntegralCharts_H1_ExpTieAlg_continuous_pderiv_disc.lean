-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.continuous_pderiv_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:31.212771+00:00
-- url     : https://prove2.me/submissions/ca471885-77df-4cd7-9843-77abde9d499b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
open scoped MvPowerSeries.WithPiTopology
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  classical
  refine continuous_pi fun n => ?_
  exact ((continuous_of_discreteTopology (f := fun x : R => x * ((n i : R) + 1))).comp
    (continuous_apply (n + Finsupp.single i 1))).congr fun f => (coeff_pderiv f n).symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
