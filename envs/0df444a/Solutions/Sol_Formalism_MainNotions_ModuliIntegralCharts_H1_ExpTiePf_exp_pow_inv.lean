-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf.exp_pow_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:15.146677+00:00
-- url     : https://prove2.me/submissions/2cc05016-7eca-4d86-a211-ee2133f6d25b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
theorem _root_.solution {S : Type} [CommRing S] [Algebra ℚ S] {σ : Type} (b : MvPowerSeries σ S)
    (hb : constantCoeff b = 0) (k : ℕ) :
    PowerSeries.subst ((k : S) • b) (PowerSeries.exp S) * (PowerSeries.subst (-b) (PowerSeries.exp S)) ^ k = 1 := by
  have hs : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have key : ∀ r : S, PowerSeries.subst (r • b) (PowerSeries.exp S) =
      PowerSeries.subst b (PowerSeries.rescale r (PowerSeries.exp S)) := by
    intro r
    rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero
        (by exact (congrArg (r * ·) PowerSeries.constantCoeff_X).trans (mul_zero r))) hs]
    congr 1
    rw [PowerSeries.subst_smul hs, PowerSeries.subst_X hs]
  have hneg : -b = (-1 : S) • b := by simp
  rw [hneg, key, key, ← PowerSeries.subst_pow hs, ← PowerSeries.subst_mul hs]
  rw [← PowerSeries.exp_pow_eq_rescale_exp, ← mul_pow]
  have h1 : PowerSeries.exp S * PowerSeries.rescale (-1 : S) (PowerSeries.exp S) = 1 := by
    have h2 := PowerSeries.exp_mul_exp_eq_exp_add (A := S) 1 (-1)
    rw [add_neg_cancel, PowerSeries.rescale_one, RingHom.id_apply] at h2
    rw [h2, PowerSeries.rescale_zero, RingHom.comp_apply, PowerSeries.constantCoeff_exp, map_one]
  rw [h1, one_pow]
  first
    | exact PowerSeries.subst_one hs
    | exact (PowerSeries.substAlgHom hs).map_one
    | simp [← PowerSeries.coe_substAlgHom hs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
