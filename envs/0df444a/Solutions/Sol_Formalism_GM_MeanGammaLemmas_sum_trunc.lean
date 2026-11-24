-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.sum_trunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.804799+00:00
-- url     : https://prove2.me/submissions/495a0623-1e67-4e59-a886-ef4d3adec946

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
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
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution {F : Type} [Field F] (D0 del : ℕ) (h : D0 ≤ del) (g : ℕ → F) :
    ∑ k ∈ range (del + 1), (if k ≤ D0 then g k else 0) = ∑ k ∈ range (D0 + 1), g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega
end Formalism.GM.MeanGammaLemmas
