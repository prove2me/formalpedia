-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.inv_start
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:49.507868+00:00
-- url     : https://prove2.me/submissions/9defc68b-d3c7-4f19-801b-21dc1321beb0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_localizationToLaurent_injective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_msg_comp_iotaL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_preimage_TLset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_rename_iotaL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mtp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_rename_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (p : ℕ) (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K) (hGt : Gt ∈ PolO v D.r D.dO)
    (hval : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt) :
    D.Inv v p θ Gt ∅ (rename (Prod.map D.iotaL id) Gt) := by
  refine ⟨?_, D.ph_rename_iotaL p Gt, ?_, fun j hj => by simp at hj, ?_⟩
  · intro α
    by_cases hα : ∃ u, Finsupp.mapDomain (Prod.map D.iotaL id) u = α
    · obtain ⟨u, rfl⟩ := hα
      rw [coeff_rename_mapDomain _ D.localizationToLaurent_injective]
      exact hGt.2 u
    · rw [coeff_rename_eq_zero _ _ _ (fun u hu => absurd ⟨u, hu⟩ hα), AddValuation.map_zero]
      exact le_top
  · intro ζ hζ
    have hex : ∃ u ∈ Gt.support, Finsupp.mapDomain (Prod.map D.iotaL id) u = ζ := by
      by_contra hc
      push_neg at hc
      rw [mem_support_iff] at hζ
      apply hζ
      apply coeff_rename_eq_zero
      intro u hu
      by_contra hne
      exact hc u (mem_support_iff.mpr hne) hu
    obtain ⟨u, hu, rfl⟩ := hex
    have hdeg := (mem_PolK_iff _ _).mp hGt.1 u hu
    refine ⟨fun t a => D.mapDomain_mw u t a, fun j hj => by simp at hj,
      fun j _ => ⟨fun b _ => ?_, fun m => ?_, fun m a => D.mapDomain_mtp u _ a⟩⟩
    · have h1 := hdeg (Sum.inl b)
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mb]
      exact h1
    · have h1 := hdeg (Sum.inr (j, m))
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mlab]
      exact h1
  · intro j _ m hm
    rw [vala_rename_iff D.iotaL D.iotaL_injective, msg_comp_iotaL, preimage_TLset]
    exact hval j m hm
end Formalism.MainNotions.PlaneGram.TwistData
