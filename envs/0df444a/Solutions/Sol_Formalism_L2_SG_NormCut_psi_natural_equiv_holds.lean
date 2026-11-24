-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.psi_natural_equiv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:39:08.912896+00:00
-- url     : https://prove2.me/submissions/c2569017-f403-4e8d-b6b1-94f9d8791fbb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_isUni_mul
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_isUni_inv
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_psiU_mul
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_norm_addChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism.L2.SG.GGMirabolic Formalism.L2.SG.NormCut.PsiNatEquivPf
namespace Formalism.L2.SG.NormCut
theorem _root_.solution : Formalism.L2.SG.NormCut.PsiNatEquiv := by
  intro F _ _ k ψ₀ x w hw
  refine ⟨?_, ?_, ?_⟩
  · by_cases hx : IsUni k x
    · unfold psiNat
      rw [if_pos (isUni_mul hx hw), if_pos hx, if_pos hw]
      exact psiU_mul ψ₀ hx hw
    · have hxw : ¬ IsUni k (x * w) := by
        intro h
        have h' := isUni_mul h (isUni_inv hw)
        rw [mul_inv_cancel_right] at h'
        exact hx h'
      unfold psiNat
      rw [if_neg hxw, if_neg hx, zero_mul]
  · by_cases hx : IsUni k x
    · unfold psiNat
      rw [if_pos (isUni_mul hw hx), if_pos hx, if_pos hw]
      exact psiU_mul ψ₀ hw hx
    · have hwx : ¬ IsUni k (w * x) := by
        intro h
        have h' := isUni_mul (isUni_inv hw) h
        rw [inv_mul_cancel_left] at h'
        exact hx h'
      unfold psiNat
      rw [if_neg hwx, if_neg hx, mul_zero]
  · unfold psiNat psiU
    rw [if_pos hw]
    first
      | (rw [Complex.conj_mul', norm_addChar]; simp)
      | (rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar]; simp)
end Formalism.L2.SG.NormCut
