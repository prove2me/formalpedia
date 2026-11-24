-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.binMatK_eval_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.066383+00:00
-- url     : https://prove2.me/submissions/a5735281-d203-4de7-b487-9a80b4649692

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_binK_eval_nat
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (F : Type) [Field F] [CharZero F] {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) (i j : Fin n) (t : ℕ) :
    (binMatK F del c i j).eval (t : F) = ∑ k ∈ range (del + 1), c i j k * (t.choose k : F) := by
  simp only [binMatK, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, binK_eval_nat]
end Formalism.GM.MeanGammaLemmas
