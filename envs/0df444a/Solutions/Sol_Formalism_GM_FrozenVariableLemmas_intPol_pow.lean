-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.intPol_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:37.601483+00:00
-- url     : https://prove2.me/submissions/78f998e3-a6ae-45d4-8417-39aae8b36ecf

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
theorem _root_.solution {F : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (k : ℕ) :
    F ^ k ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF ⊢
  obtain ⟨F₀, rfl⟩ := hF
  exact ⟨F₀ ^ k, _root_.map_pow _ _ _⟩
end Formalism.GM.FrozenVariableLemmas
