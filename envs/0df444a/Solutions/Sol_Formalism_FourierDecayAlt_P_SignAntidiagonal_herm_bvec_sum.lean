-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:35:11.146271+00:00
-- url     : https://prove2.me/submissions/a1d0fa86-b1ba-4c86-befa-6c44a943f979

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_zero_alt
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
theorem _root_.solution (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by
  unfold inWb at hyb
  unfold herm bvec wI
  by_cases hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k
  · rw [Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]
    · split_ifs with h
      · rw [mul_one, ← h]
      · exact absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k
      · have h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0 := by
          simp [Matrix.mulVec, hpk_zero_alt k r p i hi hp]
        rw [h0, mul_zero]
      · have h0 : yb i = 0 := hyb i (by omega)
        simp [h0]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro w _
    split_ifs with h
    · have hw := w.isLt
      rw [Fin.ext_iff] at h
      simp only [Fin.val_mk] at h
      exact absurd ⟨by omega, by omega⟩ hp
    · exact mul_zero _
end Formalism.FourierDecayAlt.P.SignAntidiagonal
