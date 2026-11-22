-- Prove2me | solution 1 for Formalism.CountingSumsFrames.compP_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:28.639268+00:00
-- url     : https://prove2.me/submissions/e1169206-1231-4a1e-837f-b85886f5525d

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution (Pr Qr : (σ →₀ ℕ) → Prop) (h : ∀ m, Pr m ↔ Qr m) (x : MvPolynomial σ K) :
    compP Pr x = compP Qr x := by
  obtain rfl : Pr = Qr := funext fun m => propext (h m)
  rfl
end Formalism.CountingSumsFrames
