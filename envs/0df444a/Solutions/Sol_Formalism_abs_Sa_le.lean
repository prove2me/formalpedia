-- Prove2me | solution 1 for Formalism.abs_Sa_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:19.187869+00:00
-- url     : https://prove2.me/submissions/03b81fe9-4463-405e-ae01-114f0837e0da

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Theorems.Thm_Formalism_a_mxS_eq_zero
import Theorems.Thm_Formalism_Sa_eq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
variable (a : ℕ → ℝ)
namespace Formalism
theorem _root_.solution (ha0 : a 0 = 0) (x : ℝ) : |Sa a x| ≤ ∑' n, |a n| * mxS n x := by
  have hm : ∀ n, 0 ≤ mxS n x := fun n => by
    unfold mxS
    exact le_max_right _ _
  rw [Sa_eq_tsum a ha0 x, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn),
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => by
      have h := a_mxS_eq_zero a ha0 x n hn
      rcases mul_eq_zero.mp h with h | h <;> simp [h])]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [abs_mul, abs_of_nonneg (hm n)]
end Formalism
