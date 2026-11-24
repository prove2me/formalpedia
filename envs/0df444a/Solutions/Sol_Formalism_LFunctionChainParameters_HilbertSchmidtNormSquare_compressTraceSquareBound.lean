-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.compressTraceSquareBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:34.844799+00:00
-- url     : https://prove2.me/submissions/7a75a6fc-d69a-4c8f-9ca6-d9413a8c52ac

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_Qm_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_compress
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Kp_ram
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressTraceLowerBound
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_main
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_ram
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_step
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_cor_common

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
set_option maxHeartbeats 800000
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution : CompressTraceSquareBound := by
  intro ι _ D d r B V ga Dstar sg η0 η1 e0 de hV hga hD hs0 hs hR hη0 hη0' hη1' he ha' hde0 hde hsum hS
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hS' := hS
  obtain ⟨hP, hK, hDD⟩ := hS'
  obtain ⟨hDpos, hL, hT, hF2, hF1⟩ :=
    cor_common B ga hga hD hs0 (by linarith) hR hη0 he ha' hS
  have hlow := compressTraceLowerBound ι D d r B V ga de e0 hV hga hde0 he hK hsum
  have hT2c : (Qm (Bram B V) ga * Qm (Bram B V) ga).trace.re
      ≤ (Qm B ga * Qm B ga).trace.re := by
    rw [trace_Qm_sq (Bram B V) ga hga, trace_Qm_sq B ga hga,
      Complex.ofReal_re, Complex.ofReal_re]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => ?_
    rw [Kp_ram B V ga u u']
    exact hsSq_compress (V u) (hV' u) (V u') (hV' u') _
  have ht0 := Real.sqrt_nonneg de
  have ha0 := Real.sqrt_nonneg e0
  have hsq : Real.sqrt de ^ 2 = de := Real.sq_sqrt hde0
  have ht1 : Real.sqrt de ≤ 1 / 2 := by nlinarith
  have hmul : Real.sqrt (de * e0) = Real.sqrt de * Real.sqrt e0 := Real.sqrt_mul hde0 e0
  have hT1' : (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d
      ≤ (Qm (Bram B V) ga).trace.re := by
    rw [hmul] at hlow
    rw [hsq]
    linarith
  have hb0 : 0 ≤ (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d := by
    refine mul_nonneg ?_ hT.le
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) ht0, mul_nonneg (sub_nonneg.2 ht1) ha0]
  have hX0 : 0 ≤ (1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg :=
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le)
  have hc1 := num_main hs0 (by linarith : sg ≤ 1 / 4) hη0 hη0' hη1' hL ha0 ha'
  have hc2 := num_ram hs0 hs ha0 ha' ht0 ht1
  unfold F1
  exact num_step hDpos hD hDD hX0 (hT2c.trans hF2) hb0 hT1' (by linarith [hc1, hc2])
    (by linarith)
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
