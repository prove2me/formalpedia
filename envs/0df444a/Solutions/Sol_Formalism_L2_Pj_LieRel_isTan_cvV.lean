-- Prove2me | solution 1 for Formalism.L2.Pj.LieRel.isTan_cvV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:21:35.224199+00:00
-- url     : https://prove2.me/submissions/6a8adc79-90bc-4864-9d05-8490f092bd22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Theorems.Thm_Formalism_L2_Pj_LieRel_cvV_left
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
variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
namespace Formalism.L2.Pj.LieRel
theorem _root_.solution {y : sp (R₀ := V) (DualNumber V) ⟶ G} (h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y) : IsTan (cvV y) := by
  have h' : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y = 1 := h
  have e : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y).left =
      (1 : sp (R₀ := V) V ⟶ G).left := by rw [h']
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ (cvV y).left = (1 : ptOver V V ⟶ G).left
  rw [cvV_left]
  exact e
end Formalism.L2.Pj.LieRel
