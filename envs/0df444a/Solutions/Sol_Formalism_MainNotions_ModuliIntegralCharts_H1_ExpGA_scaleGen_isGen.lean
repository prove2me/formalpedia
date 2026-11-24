-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.scaleGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:17.07526+00:00
-- url     : https://prove2.me/submissions/90e374b2-c849-4816-8d4d-bbbffacfcc85

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res h1 x) = ReciprocityTheory.ChartRestriction.G.Semi.res (h2.trans h1) x := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ← Functor.map_comp_apply])
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
theorem _root_.solution {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (v : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (hg : g.IsGen) : (scaleGen φ ε v g).IsGen := by
  intro i j
  have H := hg i j
  simp only [Formalism.L2.Pj.scaleGen, map_mul, res_res_lemma]
  rw [H]
  exact mul_left_comm _ _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
