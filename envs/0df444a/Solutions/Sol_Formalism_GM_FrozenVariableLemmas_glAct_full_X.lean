-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:42.525911+00:00
-- url     : https://prove2.me/submissions/49fe7e24-4344-4232-8943-a3ac4c01f776

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_apply

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
theorem _root_.solution (b : Fin K) (d : Fin r) :
    M.glAct p L K c ρ (X (b, d)) =
      if L.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by
  rw [glAct_full_apply, Finset.sum_eq_single b]
  · by_cases hv : L.vec b
    · by_cases hd : d = ρ <;> simp [hv, hd, pderiv_X, Pi.single_apply]
    · by_cases hd : d = c <;> simp [hv, hd, pderiv_X, Pi.single_apply]
  · intro i _ hi
    simp [pderiv_X, Pi.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ b) h
end Formalism.GM.FrozenVariableLemmas
