-- Prove2me | solution 1 for Formalism.GM.TM.wt_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:18.273413+00:00
-- url     : https://prove2.me/submissions/c2ca967b-a6e9-40f0-b6a1-2b7f239329f5

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution {N r : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) (hm : MultiDeg LL m) :
    |wt LL j c m| ≤ (LL.total : ℤ) := by
  unfold wt Letters.total
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 : (m (i, c) : ℤ) ≤ LL.deg i := by
    rw [← hm i]; push_cast
    exact_mod_cast Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (mem_univ c)
  split_ifs <;> simp <;> omega
end Formalism.GM.TM
