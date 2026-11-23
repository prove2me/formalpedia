-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.weight_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:38.210912+00:00
-- url     : https://prove2.me/submissions/b136e2d0-9bdf-4c6b-b864-e6788fee27cf

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
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {M r : ℕ} (G : Fin M → ℕ) (m : Fin M × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin M × Fin r => G x.1) m = ∑ b, G b * ∑ c, m (b, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • G i.1) (fun i => zero_smul _ _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [smul_eq_mul, mul_comm]
end Formalism.GM.FrozenVariableLemmas
