-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.sum_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:51:44.190743+00:00
-- url     : https://prove2.me/submissions/62fb384f-8a70-4a1e-b7c6-5308459ac396

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_det_row_lin
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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} {ι : Type} [Fintype ι]
    (P : (Fin m → Fin N) → Prop) [DecidablePred P] (X : Fin m → Fin N → ℂ) (i : Fin m) (η : ι → ℂ)
    (v : ι → Fin N → ℂ) (hrow : ∀ p, X i p = ∑ w, η w * v w p) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      ∑ w, η w • ∑ c : Fin m → Fin N,
        if P c then (Matrix.of fun a l => (if a = i then v w (c l) else X a (c l))).det • F c else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hP
  · rw [det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)
  · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
