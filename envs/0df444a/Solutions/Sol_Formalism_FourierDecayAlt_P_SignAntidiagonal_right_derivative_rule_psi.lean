-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.right_derivative_rule_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:21.732798+00:00
-- url     : https://prove2.me/submissions/e964aadb-551b-4924-8076-0b94e01a167d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_bvec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : RuleRightDpsi := by
  intro k r z' l j hw
  have hl := l.isLt
  have hj := j.isLt
  simp only [Formalism.FourierDecayAlt.Q.mdim, Fin.val_succ] at hj
  have heI : ∀ a : Fin r, (eI k r a).val = a.val := fun _ => rfl
  have hesI : ∀ a : Fin r, (esI k r a).val = 2 * r + k - a.val := fun _ => rfl
  have hqv : (Formalism.FourierDecayAlt.Q.posL k r l.succ j).val = j.val + l.val + 1 := by
    simp only [Formalism.FourierDecayAlt.Q.posL, Fin.val_succ]
    omega
  have hz : ∀ q : Fin (2 * r + k + 1), (q.val < r ∨ r + k < q.val) →
      herm (Hpk k r) (bvec q) z' = 0 := by
    intro q hq
    unfold herm
    show ∑ m, (star z') m * (Hpk k r *ᵥ bvec q) m = 0
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : r ≤ m.val ∧ m.val ≤ r + k
    · have h0 : (Hpk k r *ᵥ bvec q) m = 0 := by
        have e : (Hpk k r *ᵥ bvec q) m = Hpk k r m q := by
          simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
        rw [e]
        simp only [Hpk]
        rw [if_neg (fun hc => by omega), if_neg (fun hc => by omega),
          if_neg (fun hc => by rw [hc.2.2] at hm; omega)]
      rw [h0, mul_zero]
    · have h0 : z' m = 0 := hw m (by omega)
      simp [h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold InNp
    rw [heI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, bvec, Pi.single_apply, Fin.ext_iff, hv, hqv, dpsiP, heI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, dpsiP, heI, hqv]
      split_ifs <;> first
        | rfl
        | (exfalso; omega)
        | exact hw _ (by rw [hqv]; omega)
        | exact (hw _ (by rw [hqv]; omega)).symm
  · unfold InNp
    rw [hesI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf, herm_bvec_bvec]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [dpsiP, Hpk, Fin.ext_iff, hv, hqv, hesI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf]
      rw [dpsiP]
      split_ifs <;> first
        | rfl
        | (exfalso; rw [hqv, hesI] at *; omega)
        | exact hz _ (by rw [hqv]; omega)
        | (exfalso; omega)
end Formalism.FourierDecayAlt.P.SignAntidiagonal
