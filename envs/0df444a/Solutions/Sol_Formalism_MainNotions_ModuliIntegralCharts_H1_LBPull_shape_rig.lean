-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.shape_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:58.610518+00:00
-- url     : https://prove2.me/submissions/06f017c4-17e7-48d1-a54f-a462ec03c231

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K : Type} [Fintype K]
end Gen
section GenX
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {Y Z : Scheme.{0}} {K : Type} [Fintype K]
end GenX
section Sec
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
end Sec
section Val
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
end Val
section Rig
private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
end Rig
section SecComp
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
end SecComp
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
theorem _root_.solution {X T T' : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X) (hf : g ≫ f = f')
    {U : X.Opens} {W : T.Opens} (hW : W ≤ f ⁻¹ᵁ U) {V : T'.Opens} (hV : V ≤ g ⁻¹ᵁ W) {V' : T'.Opens}
    (hV' : V' ≤ f' ⁻¹ᵁ U) {O : T'.Opens} (o1 : O ≤ V) (o2 : O ≤ V') (x : Γ(X, U)ˣ) (k : ℤ) :
    res o1 (res hV (pullU g W ((res hW (pullU f U x)) ^ k))) = res o2 ((res hV' (pullU f' U x)) ^ k) := by
  subst hf
  have hA : V ≤ (g ≫ f) ⁻¹ᵁ U := fun y hy => hW (hV hy)
  simp only [map_zpow]
  congr 1
  rw [← DVR.res_pullU_comp' g f hW hV hA x, res_res_lemma, res_res_lemma]
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
