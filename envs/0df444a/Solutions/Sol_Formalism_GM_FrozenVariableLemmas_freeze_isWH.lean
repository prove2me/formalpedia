-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freeze_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:33.047337+00:00
-- url     : https://prove2.me/submissions/2cdbbad4-fbf3-4f87-8511-2b0d569edf4e

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_aeval_isWH
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_isWH_X_fst
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freezeSub_isWH
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_pol_isWH

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
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (g : Fin (N + 1) → ℕ) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freeze p LL ρ n f)
      ((n - LL.total) • g (Fin.last N) + ∑ b, (g (Fin.castSucc b) + g (Fin.last N)) * LL.deg b) := by
  exact ((isWH_X_fst g (Fin.last N) ρ).pow _).mul
    (aeval_isWH (fun x => g (Fin.castSucc x.1) + g (Fin.last N)) (fun y => g y.1) (M.freezeSub p LL ρ)
      (fun x => freezeSub_isWH p LL ρ g x) (pol_isWH p LL (fun b => g (Fin.castSucc b) + g (Fin.last N)) hf))
end Formalism.GM.FrozenVariableLemmas
