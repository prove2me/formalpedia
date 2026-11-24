-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_Kp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:34.667468+00:00
-- url     : https://prove2.me/submissions/d02be207-c92b-4ab4-bde7-ce148608ece7

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_smul

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
    (u u' : ι) : hsSq (Kp B ga u u') = ga u * ga u' * hsSq ((B u)ᴴ * B u') := by
  unfold Kp
  rw [hsSq_smul]
  have hn : ‖((Real.sqrt (ga u * ga u') : ℝ) : ℂ)‖ ^ 2 = ga u * ga u' := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (hga u) (hga u'))]
  rw [hn]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
