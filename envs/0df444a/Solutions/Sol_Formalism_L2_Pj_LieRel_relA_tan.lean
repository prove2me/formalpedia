-- Prove2me | solution 1 for Formalism.L2.Pj.LieRel.relA_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:30.991069+00:00
-- url     : https://prove2.me/submissions/86da2102-2536-47fa-943a-67b1976fe0d5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Theorems.Thm_Formalism_L2_Pj_LieRel_fst_alg
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tcoord tmap IsUnivChart tvec_tmap tcoord_spec tvec_inj list_prod_tan' tcoord_scale
  tcoord_tvec isTan_tvec isTan_scale tvec_eig_iff scaleD fB Rel liftT viaT rel_exists_w rel_exists_v rel_eq_iff
  rel_prod rel_pre tan_iff eig_iff one_left' sp JetR)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : Sp K ⟶ S) {G' : Over (Sp K)} [GrpObj G']
  {F1 : G'.left ⟶ A.left} (h1 : IsGrpPullback G' A x F1) {V : Type} [CommRing V] [Algebra V K] {G : Over (Sp V)}
  [GrpObj G] {F2 : G'.left ⟶ G.left} (h2 : IsGrpPullback G' G (fB V K) F2)
include h1 h2
namespace Formalism.L2.Pj.LieRel
theorem _root_.solution {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
  have hb : (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = (1 : Over.mk x ⟶ A).left := by
    have e : (pushHom h1 (Over.mk (𝟙 (Sp K))) 1).left =
        (1 : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x) ⟶ A).left := by
      rw [map_one]
    change (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = _ at e
    rw [e, one_left', one_left']
    simp
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← tan_iff h2 (Category.id_comp _) hwy, hwv, ← hb]
  constructor
  · intro e
    apply h1.1.hom_ext
    · rw [Category.assoc]
      exact e
    · rw [Category.assoc, Over.w w, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ G')]
      simpa using fst_alg
  · intro e
    rw [← Category.assoc, e]
end Formalism.L2.Pj.LieRel
