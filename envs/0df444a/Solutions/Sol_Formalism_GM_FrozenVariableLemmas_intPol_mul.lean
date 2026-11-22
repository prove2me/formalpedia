-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.intPol_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:08.600799+00:00
-- url     : https://prove2.me/submissions/5ab4f201-e692-4b3e-b458-6766eb475555

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
theorem _root_.solution {F G : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (hG : G ∈ M.IntPol p τ) :
    F * G ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF hG ⊢
  obtain ⟨F₀, rfl⟩ := hF
  obtain ⟨G₀, rfl⟩ := hG
  exact ⟨F₀ * G₀, _root_.map_mul _ _ _⟩
end Formalism.GM.FrozenVariableLemmas
