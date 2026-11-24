-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD.chart_at_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:12.487891+00:00
-- url     : https://prove2.me/submissions/a73f04e1-d7bc-47b1-ad5b-fde3a34c6e07

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_jet_zero_hom_ext
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
theorem _root_.solution (C : ChartAt Xo c y) : C.x 0 = 1 := by
  have hz := C.chart.zero 0
  have hid : homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
      homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S) = 𝟙 _ := by
    rw [homAt_comp, jet_zero_hom_ext ((Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)).comp jetAug) (AlgHom.id S _), homAt_id]
  calc C.x 0 = 𝟙 _ ≫ C.x 0 := (Category.id_comp _).symm
    _ = (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
          homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)) ≫ C.x 0 := by rw [hid]
    _ = homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫ 1 := by rw [Category.assoc, hz]
    _ = 1 := comp_one' _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
