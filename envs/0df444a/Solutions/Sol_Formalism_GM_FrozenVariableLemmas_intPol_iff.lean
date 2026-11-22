-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.intPol_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:50.729699+00:00
-- url     : https://prove2.me/submissions/798c2b39-aa96-49db-94a7-321c6ccab54f

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {τ : Type}
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (F : MvPolynomial τ ℚ_[p]) :
    F ∈ M.IntPol p τ ↔ ∃ F₀ : MvPolynomial τ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by
  unfold M.IntPol
  rw [LinearMap.mem_range]
  rfl
end Formalism.GM.FrozenVariableLemmas
