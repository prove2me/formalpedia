-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:18.064736+00:00
-- url     : https://prove2.me/submissions/617453f7-81a6-4de5-8943-85ce0b45fd6a

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ F = ∑ i : Fin K,
      (if L.vec i then X (i, c) * pderiv (i, ρ) F else -(X (i, ρ) * pderiv (i, c) F)) := by
  unfold M.glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_pos i.isLt]
  split_ifs <;> simp
end Formalism.GM.FrozenVariableLemmas
