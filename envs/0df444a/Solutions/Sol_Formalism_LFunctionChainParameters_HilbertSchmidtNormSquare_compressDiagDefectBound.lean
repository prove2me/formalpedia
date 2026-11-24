-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.compressDiagDefectBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:43.094135+00:00
-- url     : https://prove2.me/submissions/cf35af96-5695-4101-aa21-b8a7997e894a

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Rs_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_compress
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Kd_ram_sub

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
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution : CompressDiagDefectBound := by
  intro ι _ D d r B V ga de e0 hV hde he hK hsum
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hr : ∑ u, ((d u : ℝ) - r u) = Rs d - Rs r := by
    unfold Rs
    rw [Finset.sum_sub_distrib]
  have h1 : (1 - de) * Rs d ≤ Rs r := by
    rw [hr] at hsum
    linarith
  refine ⟨h1, ?_⟩
  have hb : ∀ u, hsSq (Kd (Bram B V) ga u - 1) ≤ e0 * (d u : ℝ) := by
    intro u
    rw [Kd_ram_sub B V ga hV u]
    exact (hsSq_compress (V u) (hV' u) (V u) (hV' u) _).trans (hK u)
  have hTd := Rs_nonneg d
  have h2 : Rs d ≤ 2 * Rs r := by
    nlinarith [mul_nonneg (sub_nonneg.2 hde) hTd]
  unfold F2
  calc ∑ u, hsSq (Kd (Bram B V) ga u - 1)
      ≤ ∑ u, e0 * (d u : ℝ) := Finset.sum_le_sum fun u _ => hb u
    _ = e0 * Rs d := by
        unfold Rs
        rw [Finset.mul_sum]
    _ ≤ 2 * e0 * Rs r := by nlinarith [mul_le_mul_of_nonneg_left h2 he]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
