-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_comb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:23.634648+00:00
-- url     : https://prove2.me/submissions/69ad545e-ffac-422b-971d-0435ba241d47

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Theorems.Thm_Formalism_L2_Pj_gfp_hcId
import Theorems.Thm_Formalism_L2_Pj_gfp_rel
import Theorems.Thm_Formalism_L2_Pj_gfp_tvec_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gfpVec x xc (e j)) a (gfpVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hg : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W' : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫
      (gfpW xc (e j) : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G)
  have hW' : ∀ j, Rel (F := 𝟙 Xo.univ.t.G.left) x x (W' j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => ReciprocityTheory.ChartRestriction.G.Chart.rel_pre _ (gfp_rel xc (e j))
  have hP := ReciprocityTheory.ChartRestriction.G.Chart.rel_prod gfp_hcId hg W' _ hW'
  rw [← gfp_tvec_sum hx a e] at hP
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext (hu j)
    have eu : (List.ofFn W').prod =
        (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := by
      rw [← eu']
      exact Over.OverMorphism.ext hprod
    rw [eu] at hP
    exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_v (gfp_rel xc cc) hP)
  · intro h
    subst h
    refine ⟨W', fun j => rfl, ?_⟩
    exact congrArg (fun q => q.left) (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_w gfp_hcId hP (gfp_rel xc _))
end Formalism.L2.Pj
