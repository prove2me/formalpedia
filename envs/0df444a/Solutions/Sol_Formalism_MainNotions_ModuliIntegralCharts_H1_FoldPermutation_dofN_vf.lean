-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_vf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:34.367137+00:00
-- url     : https://prove2.me/submissions/027b7c4f-306d-4f18-ae6b-f23731da7652

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_cz_embP
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
theorem _root_.solution (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
