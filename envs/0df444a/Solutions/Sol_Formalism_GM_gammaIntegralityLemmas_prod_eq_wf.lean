-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.prod_eq_wf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.439163+00:00
-- url     : https://prove2.me/submissions/0d8d7823-c15d-4952-8cf0-eb1f5d38f630

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) = wf (p := p) m := by
  unfold wf; exact Finsupp.prod_fintype _ _ (by simp)
end Formalism.GM.gammaIntegralityLemmas
