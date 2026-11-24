-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.det_row_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:35:10.323832+00:00
-- url     : https://prove2.me/submissions/18a4c4aa-37d1-4ec1-8b74-507690bda987

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_det_row_sum
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
theorem _root_.solution {n : ℕ} {ι : Type} [Fintype ι] (X : Fin n → Fin n → ℂ) (i : Fin n) (η : ι → ℂ)
    (v : ι → Fin n → ℂ) (hrow : ∀ l, X i l = ∑ w, η w * v w l) :
    (Matrix.of X).det = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det := by
  have h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w) := by
    ext a l
    by_cases h : a = i
    · subst h
      simp [Matrix.updateRow_self, hrow, Finset.sum_apply]
    · simp [Matrix.updateRow_ne h]
  have h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) =
      (Matrix.of X).updateRow i (v w) := by
    intro w
    ext a l
    by_cases h : a = i
    · subst h
      simp
    · simp [h, Matrix.updateRow_ne h]
  calc (Matrix.of X).det = ((Matrix.of X).updateRow i (∑ w ∈ Finset.univ, η w • v w)).det :=
        congrArg Matrix.det h1
    _ = ∑ w ∈ Finset.univ, η w * ((Matrix.of X).updateRow i (v w)).det := det_row_sum _ _ _ _ _
    _ = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det :=
        Finset.sum_congr rfl (fun w _ => by rw [h2 w])
end Formalism.FourierDecayAlt.P.SignAntidiagonal
