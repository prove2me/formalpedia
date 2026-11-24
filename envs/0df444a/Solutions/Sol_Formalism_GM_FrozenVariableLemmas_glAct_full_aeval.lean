-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:43.349911+00:00
-- url     : https://prove2.me/submissions/5b58db2e-185b-44fc-968d-47ce051b8004

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_C

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {τ : Type} (σ : τ → MvPolynomial (Fin K × Fin r) ℚ_[p])
    (hσ : ∀ x, M.glAct p L K c ρ (σ x) = 0) (f : MvPolynomial τ ℚ_[p]) :
    M.glAct p L K c ρ (aeval σ f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, glAct_full_C]
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add, hf, hg, add_zero]
  | mul_X f x hf =>
    rw [_root_.map_mul, aeval_X, glAct_full_mul, hf, hσ x, mul_zero, mul_zero, add_zero]
end Formalism.GM.FrozenVariableLemmas
