-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.Bq_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:40.879744+00:00
-- url     : https://prove2.me/submissions/dbc5f1ae-5609-4eae-add5-3bb9deec525d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (wLa : AdTy Xo a) (hwa : wLa.IsGen)
    (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) : (Bq wP a wLa wLb).IsGen := by
  have hP := fun c => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ wP hwP (Xo.univ.t.act.act c).left
  have hC := fun (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ _ Xo.univ.t.cub.isGen (lift p (lift q r)).left
  unfold Bq
  refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hP _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))
          (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hwP)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _) (hC _ _ _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwa _)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwb _))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
