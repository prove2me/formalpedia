-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dofN_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:51.613564+00:00
-- url     : https://prove2.me/submissions/09e45420-a3bd-41fc-b69a-73cca875ac20

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_ev_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_ptz_cc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_ptz_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_C_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_pderiv_mem


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
theorem _root_.solution (F : Fin d → PS R 2 d) (T : Finset (Fin n)) {b : Fin n} (hb : b ∈ T)
    (u : Fin d → R) (g : PS R n d) (hg : g ∈ subV R (Vc d T)) :
    DofN F b u g ∈ subV R (Vc d T) := by
  unfold DofN
  exact sum_mem fun j _ => mul_mem (sum_mem fun i _ =>
    mul_mem (C_mem _ _) (ev_mem _ _ (ptz_cc b) (ptz_mem T b hb) _)) (pderiv_mem _ hg)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
