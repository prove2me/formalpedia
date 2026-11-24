-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.initPart_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.814786+00:00
-- url     : https://prove2.me/submissions/5e01ef07-a2ac-4695-933f-63f1769e69d2

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (v : σ) (e o : ℕ) (f : MvPolynomial σ ℚ_[p]) (hf : HasOrder v o f) (h : e < o) :
    initPart v e f = 0 := by
  ext m
  rw [coeff_initPart, MvPolynomial.coeff_zero]
  split_ifs with hme
  · by_cases hm : m ∈ f.support
    · have := hf.1 m hm
      omega
    · simpa [MvPolynomial.mem_support_iff] using hm
  · rfl
end Formalism.GM.MeanGammaLemmas
