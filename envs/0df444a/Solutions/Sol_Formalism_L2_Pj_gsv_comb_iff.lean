-- Prove2me | solution 1 for Formalism.L2.Pj.gsv_comb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:54.957251+00:00
-- url     : https://prove2.me/submissions/c3455793-ecf3-4e74-8600-7459caf99c31

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
import Theorems.Thm_Formalism_L2_Pj_gsv_hcId
import Theorems.Thm_Formalism_L2_Pj_gsv_rel
import Theorems.Thm_Formalism_L2_Pj_gsv_inj
import Theorems.Thm_Formalism_L2_Pj_gsv_tvec_sum
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_pre
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart scaleD)
open Formalism.L2.Pj.GSR (Rel viaT liftT)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gsvVec x xc (e j)) a (gsvVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let u0 : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫ gsvW xc (e j)
  have hrel : ∀ j, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (u0 j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => Formalism.L2.Pj.GSR.rel_pre _ (gsv_rel xc (e j))
  have hprod : Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (List.ofFn u0).prod
      (tvec (x := xc) (∑ j, a j • e j)) := by
    rw [gsv_tvec_sum hx]
    first
    | exact Formalism.L2.Pj.GSR.rel_prod hc htk u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod hc u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod u0 _ hrel
  have hleft : ((List.ofFn u0).prod).left = gsvVec x xc (∑ j, a j • e j) := by
    have h : ((List.ofFn u0).prod).left ≫ 𝟙 _ =
        (tvec (x := xc) (∑ j, a j • e j)).left ≫ pullback.fst Xo.univ.t.G.hom x := hprod
    rw [Category.comp_id] at h
    exact h
  constructor
  · rintro ⟨u, hu, hprodu⟩
    have hue : u = u0 := by
      funext j
      apply Over.OverMorphism.ext
      rw [hu j]
      rfl
    subst hue
    exact gsv_inj hx (hprodu.symm.trans hleft)
  · intro h
    subst h
    exact ⟨u0, fun j => rfl, hleft⟩
end Formalism.L2.Pj
