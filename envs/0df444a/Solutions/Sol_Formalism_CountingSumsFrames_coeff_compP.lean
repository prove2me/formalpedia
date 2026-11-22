-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_compP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:17.186676+00:00
-- url     : https://prove2.me/submissions/d2c65c05-631f-44fe-9b38-ff8c4ef32e65

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {K σ : Type} [Field K]
open Classical
namespace Formalism.CountingSumsFrames
theorem _root_.solution (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (compP Pr x) = if Pr m then coeff m x else 0 := by
  classical
  unfold compP
  rw [coeff_sum, Finset.sum_eq_single m]
  · by_cases h : Pr m <;> simp [h, coeff_monomial]
  · intro b _ hbm
    by_cases h : Pr b <;> simp [h, coeff_monomial, hbm]
  · intro hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    by_cases h : Pr m <;> simp [h, hm]
end Formalism.CountingSumsFrames
