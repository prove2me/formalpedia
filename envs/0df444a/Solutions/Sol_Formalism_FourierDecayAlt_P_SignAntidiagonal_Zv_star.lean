-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.Zv_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:52.554381+00:00
-- url     : https://prove2.me/submissions/24779782-ccfc-4638-a958-e907d33deefd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_Ym_apply
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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy0 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hdet : (Ym k r j hj y).det ≠ 0) (b : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Zv k r j hj y b q = if b.val = 2 * r + k - q.val then 1 else 0 := by
  by_cases hc : 2 * r + k - q.val < j
  · have hq' : q = esI k r (Fin.castLE hj ⟨2 * r + k - q.val, hc⟩) := by ext; simp [esI]; omega
    have hGY : (Ym k r j hj y)⁻¹ * Ym k r j hj y = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    have := congrFun (congrFun hGY b) ⟨2 * r + k - q.val, hc⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    unfold Zv
    rw [hq']
    simp only [Ym_apply] at this
    rw [this]
    congr 1
    apply propext; constructor
    · intro h; subst h; simp only [esI, Fin.val_castLE]; omega
    · intro h; ext; simp only [esI, Fin.val_castLE] at h; simp only; omega
  · unfold Zv
    rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro a _
    rw [show q = esI k r ⟨2 * r + k - q.val, by omega⟩ by ext; simp [esI]; omega, hy0 a _ (by simp; omega), mul_zero]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
