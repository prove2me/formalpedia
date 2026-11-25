-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_Zv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:36:54.241798+00:00
-- url     : https://prove2.me/submissions/c8bfd6c5-42b2-46e4-9ae7-02fc1f153def

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_expand
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
    (hiso : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b b' : Fin j) :
    herm (Hpk k r) (Zv k r j hj y b') (Zv k r j hj y b) = 0 := by
  have h : herm (Hpk k r) (Zv k r j hj y b') (Zv k r j hj y b) =
      ∑ a, ∑ a', star ((Ym k r j hj y)⁻¹ b a') * (Ym k r j hj y)⁻¹ b' a * herm (Hpk k r) (y a) (y a') := by
    simp only [herm_expand, Zv, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [h]
  simp [hiso]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
