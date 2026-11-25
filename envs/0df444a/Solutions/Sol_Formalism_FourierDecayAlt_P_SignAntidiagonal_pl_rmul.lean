-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:41:33.394404+00:00
-- url     : https://prove2.me/submissions/6e4abbb4-dc19-465a-aa0f-ea507c1d32e3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
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
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {t : ℕ} {f : ℂ → A} (e : A) (hf : PolyLe t f) : PolyLe t (fun u => f u * e) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => C l * e, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
end Formalism.FourierDecayAlt.P.SignAntidiagonal
