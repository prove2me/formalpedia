-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.pullGen_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:01.510454+00:00
-- url     : https://prove2.me/submissions/a0bf4a63-f614-4530-9349-53581796eaa2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
section Alg
variable {S : Type} [CommRing S] {d : ℕ}
end Alg
section Unit
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
end Unit
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
private theorem app_res_top_lemma {Y Z : Scheme.{0}} (h : Z ⟶ Y) (W : Y.Opens) {W' : Z.Opens}
    (hW : W' ≤ h ⁻¹ᵁ W) (v : Γ(Y, ⊤)) :
    (Z.presheaf.map (homOfLE hW).op).hom ((h.app W).hom ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom v)) =
      (Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom (h.appTop.hom v) := by
  have e : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ h.app W ≫ Z.presheaf.map (homOfLE hW).op =
      h.appTop ≫ Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom v) e
end Geo
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (v : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen Xo.univ.t.PP.L φ ε (scaleGen φ ε v g) h =
      scaleGen (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen Xo.univ.t.PP.L φ ε g h) := by
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.LB.pullGen, Formalism.L2.Pj.scaleGen]
  congr 1
  funext j
  rw [map_mul, map_mul]
  congr 1
  apply Units.ext
  first
  | exact app_res_top_lemma h _ _ v.val
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     exact app_res_top_lemma h _ _ v.val)
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
