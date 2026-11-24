-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.low_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:48.197874+00:00
-- url     : https://prove2.me/submissions/c47494f3-0dc3-4589-951f-1cd9c4a283cb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_Formalism_FG_SolveVAux_low_add


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution {τ ι : Type} {N : ℕ} (s : Finset ι) {p : ι → MvPowerSeries τ S} (hp : ∀ i ∈ s, Low N (p i)) :
    Low N (∑ i ∈ s, p i) := by
  exact Finset.sum_induction _ (Low N) (fun _ _ h1 h2 => low_add h1 h2) (fun e _ => by simp) hp
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
