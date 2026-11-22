-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.intPol_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:11.303814+00:00
-- url     : https://prove2.me/submissions/3c275cef-a508-4ac1-a040-d0e9952799c3

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff

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
theorem _root_.solution (x : τ) : (X x : MvPolynomial τ ℚ_[p]) ∈ M.IntPol p τ := by
  rw [intPol_iff]
  exact ⟨X x, MvPolynomial.map_X _ _⟩
end Formalism.GM.FrozenVariableLemmas
