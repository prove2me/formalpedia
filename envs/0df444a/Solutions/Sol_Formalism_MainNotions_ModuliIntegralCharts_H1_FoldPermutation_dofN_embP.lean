-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_embP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:43.502957+00:00
-- url     : https://prove2.me/submissions/8700c07b-3ff3-454b-8b97-8d4173f1e5dd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_cz_embP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_pderiv_embP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_ev_ptz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
variable {k : Type} [CommRing k] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
theorem _root_.solution (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
