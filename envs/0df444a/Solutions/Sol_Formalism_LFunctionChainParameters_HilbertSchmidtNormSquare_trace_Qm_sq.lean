-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trace_Qm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:42.143264+00:00
-- url     : https://prove2.me/submissions/88a59444-4662-4d28-98b4-947dee1e2c04

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_conjTranspose_mul_self
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_Kp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ) := by
  have key : ∀ u u', ((((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)) * (((ga u' : ℝ) : ℂ) • (B u' * (B u')ᴴ))).trace
      = ((hsSq (Kp B ga u u') : ℝ) : ℂ) := by
    intro u u'
    have h2 : (B u * (B u)ᴴ * (B u' * (B u')ᴴ)).trace
        = (((B u)ᴴ * B u')ᴴ * ((B u)ᴴ * B u')).trace := by
      rw [Matrix.trace_mul_comm ((B u)ᴴ * B u')ᴴ, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (B u)]
      simp only [Matrix.mul_assoc]
    rw [hsSq_Kp B ga hga u u']
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [h2, trace_conjTranspose_mul_self]
    simp only [Complex.ofReal_mul]
    ring
  unfold Qm
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  rw [Matrix.trace_mul_comm]
  exact key u u'
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
