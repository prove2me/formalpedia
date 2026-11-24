-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.const_expS_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:19.069208+00:00
-- url     : https://prove2.me/submissions/c98a11c4-0839-4a9f-b0e7-c0cc8438bdf7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
theorem _root_.solution {d' : ℕ} (g : MvPowerSeries (Fin 1 × Fin d') S)
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (Germ.FB.expS S (-g)) = 1 := by
  have hg' : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg, neg_zero]
  have ha : PowerSeries.HasSubst (-g) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero hg'
      | exact PowerSeries.hasSubst_of_constantCoeff_zero hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hg']; exact IsNilpotent.zero)
  show MvPowerSeries.constantCoeff (PowerSeries.subst (-g) (PowerSeries.exp S)) = 1
  rw [PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    simp [map_pow, map_neg, hg, zero_pow hd]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
