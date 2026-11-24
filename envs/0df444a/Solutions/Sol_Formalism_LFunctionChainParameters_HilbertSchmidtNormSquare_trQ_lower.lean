-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trQ_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:31.58021+00:00
-- url     : https://prove2.me/submissions/9bd58991-9143-4285-9e5d-2cac4d942bc6

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_Qm
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_traceLowerBound
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_le_of_sq

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
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {e0 : ℝ} (he : 0 ≤ e0) (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  have hu : ∀ u, (1 - Real.sqrt e0) * (d u : ℝ) ≤ (Kd B ga u).trace.re := by
    intro u
    have h1 := traceLowerBound (d u) (Kd B ga u)
    have h2 := hsNorm_le_of_sq _ he (hK u)
    have h3 : Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ) = d u := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (d u : ℝ))
    have h5 : Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ)) = Real.sqrt e0 * d u := by
      rw [show Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ))
          = Real.sqrt e0 * (Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ)) by ring, h3]
    linarith
  rw [trace_Qm B ga hga, Complex.re_sum]
  unfold Rs
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => hu u
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
