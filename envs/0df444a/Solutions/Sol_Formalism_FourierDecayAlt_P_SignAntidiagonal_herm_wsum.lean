-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_wsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:44.804607+00:00
-- url     : https://prove2.me/submissions/ce819b62-e7e2-4fcb-845a-5b2eb87edb05

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
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
theorem _root_.solution (k r : ℕ) (v y : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    herm (Hpk k r) v y = ∑ w : Fin (k + 1), v (wI k r w) * herm (Hpk k r) (bvec (wI k r w)) y := by
  have hv' : v = ∑ w : Fin (k + 1), v (wI k r w) • bvec (wI k r w) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, smul_eq_mul]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [Finset.sum_eq_single ⟨i.val - r, by omega⟩]
      · have e : wI k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [wI]; omega)
        rw [e, Pi.single_eq_same, mul_one]
      · intro w _ hw
        rw [Pi.single_eq_of_ne, mul_zero]
        intro e
        apply hw
        apply Fin.ext
        have := congrArg Fin.val e
        simp only [wI, Fin.val_mk] at this ⊢
        omega
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro w _
      rw [Pi.single_eq_of_ne, mul_zero]
      intro e
      have := congrArg Fin.val e
      simp only [wI] at this
      omega
  conv_lhs => rw [hv']
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
