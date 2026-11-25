-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_dg_outside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:56.614886+00:00
-- url     : https://prove2.me/submissions/bfeedca2-ad4b-42f0-a738-2d455dbda6f7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_coefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul_left_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_coefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_monomial_nonneg_of_free

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
variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (g : (L × Fin r →₀ ℕ) → K) (n θ : ℝ)
    (h : ∀ μ, eOut out μ = μ → ∀ G : MvPolynomial (L × Fin r) K, vala sg S θ G →
      vala sg S (θ - n) (dg (fun β => g (μ + β)) G))
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) : vala sg S (θ - n) (dg g F) := by
  conv => rw [sum_coefOut out F, map_sum]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  rw [dg_monomial_mul]
  refine vala_mul_left_nonneg (valS_monomial_nonneg_of_free _ _ ?_)
    (h _ (eOut_eOut out α) _ (vala_coefOut out hout _ hF))
  intro i hi a
  rw [eOut_apply, if_neg (hout i hi)]
end Formalism.MainNotions.PlaneGram
