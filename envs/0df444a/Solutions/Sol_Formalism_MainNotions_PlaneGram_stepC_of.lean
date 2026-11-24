-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepC_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:50.647753+00:00
-- url     : https://prove2.me/submissions/4d39c91a-9a2b-43ff-ba4f-1e54b8bc19ae

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_of_mem_support_lin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_inv_all
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Sp_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_Sp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_integral_Sp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_goodE_splitE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_vala_Sp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_YPset_subset_Yset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_msg_of_mem_Yset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_superset_vec


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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hV2 : V2 K)
    (hSeg : SegStep K v p) : StepC K v p := by
  intro hD D hr hJ θ Gt hGt hval
  haveI : NeZero D.r := ⟨by omega⟩
  obtain ⟨Z, hi, hph, hsup, hY, -⟩ := D.inv_all hSeg hD hr hJ θ Gt hGt hval Finset.univ
  have hp : 0 < p := hD.prime.pos
  refine ⟨D.Sp p Z, D.integral_Sp v p hi, ?_, by rw [D.ph_Sp, hph], ?_⟩
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, h2⟩ := exists_of_mem_support_lin (D.Sp p) Z hζ'
    rw [D.Sp_monomial] at h2
    have h3 := support_monomial_subset h2
    rw [Finset.mem_singleton] at h3
    rw [h3]
    exact D.goodE_splitE hp (hsup ζ hζ).1 fun j => (hsup ζ hζ).2.1 j (Finset.mem_univ j)
  · intro j m hm
    refine D.vala_Sp p j m ?_
    exact vala_superset_vec hV2 (D.YPset_subset_Yset j m) (fun i hi hn => D.msg_of_mem_Yset hi hn)
      (hY j (Finset.mem_univ j) m hm)
end Formalism.MainNotions.PlaneGram
