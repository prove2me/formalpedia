-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.scale_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:40.459802+00:00
-- url     : https://prove2.me/submissions/1ecb616f-757d-47b0-b353-55a0633dd89d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) : (scaleGenG t φ ε u g).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hg i j)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
    refine (gm_res _ y _ hy _).trans ((map_mul _ _ _).trans ?_)
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (map_mul _ _ _)))).symm
    refine (congrArg₂ (· * ·) (gm_res _ y le_top hy.1 u) e).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (gm_res _ y le_top hy.2 u).symm rfl))
    exact _root_.mul_left_comm _ _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
