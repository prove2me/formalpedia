-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.hermitian_insertion_vector_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:24.994096+00:00
-- url     : https://prove2.me/submissions/7044cd41-bda7-4edd-9eea-64c06d29a9e6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_insertion_vector_zero_off_index
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_tau_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_val
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
  · rw [insertion_vector_zero_off_index m i Vc l hW.1 (by intro h; rw [h] at hW; simp [esI] at hW; omega)]; simp
  · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
