-- Prove2me | solution 1 for Formalism.L2.Pj.gsv_eig_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:19.909943+00:00
-- url     : https://prove2.me/submissions/e10768d4-c8b3-45f6-bdb3-0957e69d861b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gsvVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  have e1 : ∀ a : 𝓞 E, ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    intro a
    simp
    first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  have key : ∀ a : 𝓞 E, (gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left =
      spMap (epsMul (algebraMap c.F L (embK c τ a))) ≫ gsvVec x xc cc) ↔
      (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) =
        ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (algebraMap c.F L (embK c τ a))) ≫ tvec (x := xc) cc) := by
    intro a
    constructor
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp only [Over.comp_left, Category.assoc, e1]
        simp only [gsvVec] at h
        rw [← Category.assoc, h]
        rfl
      · exact (Over.w _).trans (Over.w _).symm
    · intro h
      have h' := congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) h
      simp only [Over.comp_left, Category.assoc, e1] at h'
      simp only [gsvVec, Category.assoc]
      exact h'
  simp only [IsEigAt, key, eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff ..
end Formalism.L2.Pj
