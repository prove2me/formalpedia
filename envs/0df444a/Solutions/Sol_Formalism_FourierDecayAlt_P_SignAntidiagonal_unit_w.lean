-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.unit_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:16.117286+00:00
-- url     : https://prove2.me/submissions/cdd62af6-2d26-4510-ada7-cd6b3f308f16

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_col_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_W_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_unit_entry
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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hr : 1 ≤ r) (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w w * X w (esI k r ⟨r - 1, by omega⟩) = -star (X (eI k r ⟨r - 1, by omega⟩) w) := by
  have hcol : ∀ l, Hpk k r l (esI k r ⟨r - 1, by omega⟩) = if l = eI k r ⟨r - 1, by omega⟩ then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r w l = if l = w then Hpk k r w w else 0 := fun l => hpk_W_row w l hw
  have h := unit_entry X hU w (esI k r ⟨r - 1, by omega⟩)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Finset.sum_eq_single w (fun l _ hl => by rw [hrow l, if_neg hl, zero_mul])
    (fun h' => absurd (Finset.mem_univ w) h')] at h
  linear_combination h
end Formalism.FourierDecayAlt.P.SignAntidiagonal
