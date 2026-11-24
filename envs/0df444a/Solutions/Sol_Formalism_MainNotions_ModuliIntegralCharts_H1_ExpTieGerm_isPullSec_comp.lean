-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.isPullSec_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:21.588847+00:00
-- url     : https://prove2.me/submissions/0f82f602-901d-441d-9fca-303b7e5b3997

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_pullSec_stalk

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
private theorem gs_idRes_lemma {X Y : Scheme.{0}} (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hV : W ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (x : Γ(X, U)) :
    gs (𝟙 Y) y W ((Y.presheaf.map (homOfLE hV).op).hom ((h.app U).hom x)) = gs h y U x := by
  rw [gs_res (𝟙 Y) y hV hy, gs_pull (𝟙 Y) h y U (hV hy), Category.id_comp]
section Corr
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
end Corr
section Xo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
end Xo
section Pull
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
end Pull
section Val
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
end Val
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : (h2 ▷ A).left y ∈ (LPow A L a T2).U j :=
    chart_le_res A L (h2 ▷ A) (whiskerRight_snd _ _) a j hy
  rw [GermD.pullSec_stalk (A := A) (L := L) a e2 (𝟙 _) y j hy, Category.id_comp,
    GermD.pullSec_stalk (A := A) (L := L) a e1 (h2 ▷ A).left y j hy2,
    gs_idRes_lemma _ _ y hy, comp_whiskerRight, Over.comp_left]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
