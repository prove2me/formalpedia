-- Prove2me | solution 1 for Formalism.L2.Pj.LieRel.relA_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:58:39.61133+00:00
-- url     : https://prove2.me/submissions/03220843-d031-494d-a758-32c8faaf01a5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
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
    (h : RelA x F1 F2 v y) (a : G' ⟶ G') (aA : A ⟶ A) (b : G ⟶ G) (h1a : a.left ≫ F1 = F1 ≫ aA.left)
    (h2a : a.left ≫ F2 = F2 ≫ b.left) (s : K) :
    v.left ≫ aA.left = spMap (epsMul s) ≫ v.left ↔
      y ≫ (Over.pullback (fB V K)).map b = ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s) ≫ y := by
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← eig_iff h2 a b h2a s hwy, hwv]
  constructor
  · intro e
    apply h1.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, h1a]
      rw [Category.assoc] at e
      exact e
    · rw [Over.comp_left, Category.assoc, Over.w a, Category.assoc, Over.w w]
      show (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _ =
        spMap (epsScale s) ≫ (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _
      simp only [Category.comp_id]
      exact (epsMul_alg s).symm
  · intro e
    rw [Category.assoc, ← h1a, ← Category.assoc, ← Over.comp_left, e, Category.assoc]
    rfl
end Formalism.L2.Pj.LieRel
