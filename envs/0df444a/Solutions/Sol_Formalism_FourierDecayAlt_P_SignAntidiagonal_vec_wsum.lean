-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.vec_wsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:32.635027+00:00
-- url     : https://prove2.me/submissions/d68429d3-0773-4dd7-ae81-564def7660bf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
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
theorem _root_.solution (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (p : Fin (2 * r + k + 1)) :
    v p = ∑ w : Fin (k + 1), v (wI k r w) * (if p = wI k r w then 1 else 0) := by
  by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
  · rw [Finset.sum_eq_single ⟨p.val - r, by omega⟩]
    · have : p = wI k r ⟨p.val - r, by omega⟩ := by ext; simp [wI]; omega
      rw [if_pos this, mul_one, ← this]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; apply hb; ext; simp only [h, wI]; omega
    · simp
  · rw [hv p (by omega)]; symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg, mul_zero]
    intro h; apply hp; rw [h]; simp only [wI]; omega
end Formalism.FourierDecayAlt.P.SignAntidiagonal
