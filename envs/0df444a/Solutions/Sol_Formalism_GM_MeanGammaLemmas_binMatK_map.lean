-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.binMatK_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:58.107921+00:00
-- url     : https://prove2.me/submissions/07ce95ad-87b6-47c4-84e8-143763136202

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_binK_map
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
theorem _root_.solution (F L : Type) [Field F] [Field L] (φ : F →+* L) {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) :
    binMatK L del (fun i j k => φ (c i j k)) = (binMatK F del c).map (Polynomial.map φ) := by
  funext i j
  simp only [binMatK, Matrix.map_apply, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, binK_map]
end Formalism.GM.MeanGammaLemmas
