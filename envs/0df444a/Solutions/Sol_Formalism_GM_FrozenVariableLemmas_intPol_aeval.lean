-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.intPol_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:44.638173+00:00
-- url     : https://prove2.me/submissions/53bc801b-f802-4554-840a-9c52bfa68815

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul

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
theorem _root_.solution {υ : Type} (σ : υ → MvPolynomial τ ℚ_[p]) (hσ : ∀ x, σ x ∈ M.IntPol p τ)
    {f : MvPolynomial υ ℚ_[p]} (hf : f ∈ M.IntPol p υ) : aeval σ f ∈ M.IntPol p τ := by
  rw [intPol_iff] at hf
  obtain ⟨f₀, rfl⟩ := hf
  induction f₀ using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, aeval_C, MvPolynomial.algebraMap_eq, intPol_iff]
    exact ⟨C a, MvPolynomial.map_C _ _⟩
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add]
    exact Submodule.add_mem _ hf hg
  | mul_X f x hf =>
    rw [_root_.map_mul, MvPolynomial.map_X, _root_.map_mul, aeval_X]
    exact intPol_mul p hf (hσ x)
end Formalism.GM.FrozenVariableLemmas
