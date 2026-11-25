-- Prove2me | solution 1 for Formalism.L2.Pj.int_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:50.637802+00:00
-- url     : https://prove2.me/submissions/3177a978-233e-4a6c-9779-fd4b203e8b16

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieFreePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanBC_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (T : CDVR) (io : c.F →+* T.Fr) (τ : E →+* ℂ) (a : 𝓞 E) :
    ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) := by
  obtain ⟨p, hp, hpa⟩ := NumberField.RingOfIntegers.isIntegral a
  refine IsIntegrallyClosed.isIntegral_iff.1 ⟨p.map (Int.castRingHom T.V), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hf : (algebraMap T.V T.Fr).comp (Int.castRingHom T.V) =
      (io.comp (embK c τ)).comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
  rw [hf]
  have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ (𝓞 E)) (io.comp (embK c τ)) a
  rw [hpa, map_zero] at h3
  exact h3.symm
end Formalism.L2.Pj
