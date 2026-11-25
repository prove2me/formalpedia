-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.pderiv_embP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:59.919311+00:00
-- url     : https://prove2.me/submissions/d2894c28-2c5a-47db-a43f-5fdebc92a911

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FoldPermutation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FoldPermutation_cz_embP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt


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
theorem _root_.solution {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv k (e b, j) (ev (embP e) g) = ev (embP e) (pderiv k (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
