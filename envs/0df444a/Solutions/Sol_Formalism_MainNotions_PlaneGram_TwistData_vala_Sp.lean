-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.vala_Sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:50.788431+00:00
-- url     : https://prove2.me/submissions/5d06dc75-e968-4e09-8837-4632aec4eb47

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_not_labB_of_mem_Yset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_add_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_coefOut_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_monomial_nonneg_of_vec
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le


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
theorem _root_.solution (p : ℕ) (j : Fin D.J) (m : Fin D.r) {θ : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : vala D.msg (D.Yset j m) θ Z) : vala D.msg (D.Yset j m) θ (D.Sp p Z) := by
  have key : D.Sp p Z = ∑ μ ∈ Z.support.image (eOut (fun i => D.labB i = true)),
      coefOut (fun i => D.labB i = true) μ Z * monomial (D.splitE p μ) 1 := by
    simp only [coefOut, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm, Sp, lsup_apply]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα), monomial_mul, mul_one,
      ← splitE_eq, smul_monomial, smul_eq_mul, mul_one]
  have hle : valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) (D.Sp p Z) := by
    rw [key]
    refine Finset.sum_induction _ (fun F => valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) F)
      (fun F G hF hG => le_trans (le_min hF hG) (valS_add_le _ _ _ _)) ?_ ?_
    · simp [valS]
    · intro μ hμ
      have h1 := valS_coefOut_le (K := K) (r := D.r) (fun i => D.labB i = true) D.msg (D.Yset j m)
        (fun i hi => D.not_labB_of_mem_Yset hi) μ Z
      have h2 : 0 ≤ valS D.msg (D.Yset j m) (monomial (D.splitE p μ) (1 : K)) := by
        apply valS_monomial_nonneg_of_vec
        intro i a h
        rcases i with b | t
        · exfalso
          apply h
          obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hμ
          show D.splitE p (eOut _ α) (D.mb b, a) = 0
          rw [splitE_mb, eOut_apply]
          simp [labB, mb]
        · rfl
      calc valS D.msg (D.Yset j m) Z = valS D.msg (D.Yset j m) Z + 0 := (add_zero _).symm
        _ ≤ _ := add_le_add h1 h2
        _ ≤ _ := valS_mul_le _ _ _ _
  exact le_trans hZ (toR_mono hle)
end Formalism.MainNotions.PlaneGram.TwistData
