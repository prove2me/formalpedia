-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.constantCoeff_polyAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:26.986879+00:00
-- url     : https://prove2.me/submissions/41ef28f8-af2d-4278-8cd9-1273cb7090d3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_foldr
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4

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
theorem _root_.solution {S : Type} [CommRing S] {d n : ℕ} {ι : Type} [Fintype ι] (e : ι → Fin d)
    (he : Function.Injective e) (P : MvPolynomial (ι × Fin n) S) (G : Germ.PS S n d) :
    constantCoeff (TB.polyAdd (fun l => Pi.single (e l) 1) P G) =
      ∑ m ∈ P.support, P.coeff m * ((∏ p, ((m p).factorial : S)) *
        coeff (∑ p, m p • Finsupp.single (p.2, e p.1) 1) G) := by
  classical
  unfold TB.polyAdd
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C]
  congr 1
  simp only [dAdd_single']
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_foldr (fun p : ι × Fin n => (p.2, e p.1)) m G _ (Finset.nodup_toList _) ?_ 0 (fun _ _ => by simp),
    zero_add, Finset.prod_map_toList, Finset.sum_map_toList]
  intro p _ q _ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (he h.2) h.1
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
