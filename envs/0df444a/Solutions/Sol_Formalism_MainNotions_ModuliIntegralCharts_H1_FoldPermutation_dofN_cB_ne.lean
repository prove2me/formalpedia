-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_cB_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:32.291522+00:00
-- url     : https://prove2.me/submissions/e7809479-5093-4b6f-9837-815d4e98426e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_pderiv_ev_embP_of_notMem_range

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
theorem _root_.solution (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
