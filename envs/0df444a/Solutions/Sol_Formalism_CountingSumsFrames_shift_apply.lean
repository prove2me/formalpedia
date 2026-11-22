-- Prove2me | solution 1 for Formalism.CountingSumsFrames.shift_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:38.164924+00:00
-- url     : https://prove2.me/submissions/a1c26be0-9357-412c-8275-054a78977a27

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
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames
theorem _root_.solution [DecidableEq σ] (m : σ →₀ ℕ) (u v w : σ) (hv : 1 ≤ m v) :
    ((((Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ)) w : ℕ) : ℤ) =
      (m w : ℤ) + (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega
end Formalism.CountingSumsFrames
