-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_mulu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:05.155744+00:00
-- url     : https://prove2.me/submissions/ef54a7ee-4482-418e-bdec-64adc905c331

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
theorem _root_.solution {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) (fun u => f u * algebraMap ℂ A u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩
  dsimp only
  rw [hC, Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
