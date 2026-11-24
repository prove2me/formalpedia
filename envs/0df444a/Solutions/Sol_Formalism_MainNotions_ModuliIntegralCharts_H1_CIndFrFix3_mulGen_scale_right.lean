-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.mulGen_scale_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:49.503034+00:00
-- url     : https://prove2.me/submissions/46e8fd04-5b89-4bb3-8ee2-a25e2b48b316

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
private theorem res_res_top_lemma {X : Scheme.{0}} {V W : X.Opens} (h2 : W ≤ V) (x : Γ(X, ⊤)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : V ≤ ⊤) x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : W ≤ ⊤) x := by
  apply Units.ext
  have e : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h2).op =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom x.val) e
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
theorem _root_.solution {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ Xo.univ.t.G.left)) (ε' : K' → ℤ) (w : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')) :
    LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g (scaleGen φ' ε' w g') =
      scaleGen _ _ w (LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g g') := by
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.LB.mulGen, Formalism.L2.Pj.scaleGen]
  congr 1
  funext j
  rw [map_mul]
  erw [res_res_top_lemma]
  exact mul_left_comm _ _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
