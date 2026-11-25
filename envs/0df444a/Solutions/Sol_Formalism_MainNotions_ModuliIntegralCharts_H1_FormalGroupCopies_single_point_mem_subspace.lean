-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.single_point_mem_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:40.113423+00:00
-- url     : https://prove2.me/submissions/20e4b623-bfd3-4314-a4a1-9add6cabe27c

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
theorem _root_.solution (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) :
    ∀ (q : Fin 1) (i : Fin d), (![pt R d b] : Fin 1 → Pt R n d) q i ∈ subV R (Vc d T) := by
  intro q i
  fin_cases q
  show OnV (Vc d T) (pt R d b i)
  unfold OnV pt
  intro e he p hp
  rw [MvPowerSeries.coeff_X] at he
  split_ifs at he with h
  · subst h
    have hp' := Finsupp.support_single_subset hp
    rw [Finset.mem_singleton] at hp'
    subst hp'
    exact hb
  · exact absurd rfl he
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
