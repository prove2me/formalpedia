-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_outside_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:42.46965+00:00
-- url     : https://prove2.me/submissions/8f3f32fe-1985-44fa-8aa2-4e9a754a22ca

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_sum_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_mul_coefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_coefOut_le

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
variable (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (Φ F) := by
  have hΦ : Φ F = ∑ μ ∈ F.support.image (eOut out), Φ (monomial μ 1) * coefOut out μ F := by
    rw [sum_mul_coefOut out (fun μ => Φ (monomial μ 1)) F]
    conv_lhs => rw [F.as_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have : monomial α (F.coeff α) = F.coeff α • (monomial α (1 : K)) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, h1 α, smul_eq_C_mul]
    have h3 : monomial (eIn out α) (F.coeff α) = C (F.coeff α) * monomial (eIn out α) (1 : K) := by
      rw [C_mul_monomial, mul_one]
    rw [h3]; ring
  rw [hΦ]
  refine valS_sum_le sg S _ _ _ fun μ hμ => ?_
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  refine le_trans ?_ (valS_mul_le sg S _ _)
  calc valS sg S F = 0 + valS sg S F := (zero_add _).symm
    _ ≤ _ := add_le_add (h2 α) (valS_coefOut_le out sg S hout _ F)
end Formalism.MainNotions.PlaneGram
