-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.val_encP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:48:01.072486+00:00
-- url     : https://prove2.me/submissions/1cbef977-da6a-440d-9522-71e249b3cf9c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {S : Type} [CommRing S] (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ) :
    (∏ p, ((Finsupp.equivMapDomain (ltEquiv Dw n) m p).factorial : S)) *
        coeff (∑ p, Finsupp.equivMapDomain (ltEquiv Dw n) m p • Finsupp.single (p.2, ltIdx Dw p.1) 1) G =
      mVal G m := by
  classical
  unfold mVal colIdx
  congr 1
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    exact Fintype.prod_equiv (ltEquiv Dw n).symm _ _ (fun p => by simp [Finsupp.equivMapDomain_apply])
  · congr 2
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Fintype.sum_equiv (ltEquiv Dw n).symm _ _ (fun p => ?_)
    rw [Finsupp.equivMapDomain_apply, Finsupp.smul_single_one] <;> rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
