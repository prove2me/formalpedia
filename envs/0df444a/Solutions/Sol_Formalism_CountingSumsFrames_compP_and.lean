-- Prove2me | solution 1 for Formalism.CountingSumsFrames.compP_and
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:28.576826+00:00
-- url     : https://prove2.me/submissions/1846adff-19d9-43f3-9335-8e05b05cf6f9

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution (Pr Qr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) :
    compP (fun m => Pr m ∧ Qr m) x = compP Pr (compP Qr x) := by
  ext m
  simp only [coeff_compP]
  by_cases h1 : Pr m <;> by_cases h2 : Qr m <;> simp [h1, h2]
end Formalism.CountingSumsFrames
