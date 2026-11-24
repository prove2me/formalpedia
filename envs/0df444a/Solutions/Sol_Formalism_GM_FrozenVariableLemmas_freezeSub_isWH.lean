-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freezeSub_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:41.451812+00:00
-- url     : https://prove2.me/submissions/fc75c9a6-3154-4956-8ce2-b0a1bc4a530d

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_isWH_of_eq
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_isWH_X_fst

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (g : Fin (N + 1) → ℕ) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freezeSub p LL ρ x)
      (g (Fin.castSucc x.1) + g (Fin.last N)) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact IsWeightedHomogeneous.sum _ _ _ (fun c' _ => (isWH_X_fst g _ c').mul (isWH_X_fst g _ c'))
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ ρ)) (add_comm _ _)
  · rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ ?_
    · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
    · exact (isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)
end Formalism.GM.FrozenVariableLemmas
