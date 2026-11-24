-- Prove2me | solution 1 for Formalism.IncomingBounds.factorialSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:12.763296+00:00
-- url     : https://prove2.me/submissions/c6eb04d3-df68-4cf9-bbb4-636b6ae391f7

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : FactSplit := by
  intro l hl i x
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hl0 : (l : ℚ) ≠ 0 := by
      have : (0 : ℚ) < l := by exact_mod_cast (show 0 < l by omega)
      exact this.ne'
    have hne : (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hl0) (by exact_mod_cast Nat.factorial_ne_zero _)
    have hsq : ((-1 : ℚ) ^ (l ^ i * x)) * ((-1 : ℚ) ^ (l ^ i * x)) = 1 := by
      rw [← mul_pow]; norm_num
    have key : (((l ^ (i + 1) * x).factorial : ℕ) : ℚ) =
        (-1) ^ (l ^ i * x) * (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) *
          uFac l (l ^ i * x) := by
      unfold uFac
      have h1 : l ^ (i + 1) * x = l * (l ^ i * x) := by ring
      rw [h1]
      calc (((l * (l ^ i * x)).factorial : ℕ) : ℚ)
          = ((-1 : ℚ) ^ (l ^ i * x) * (-1) ^ (l ^ i * x)) * ((l * (l ^ i * x)).factorial : ℚ) *
              (((l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ)) /
                ((l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ))) := by
            rw [hsq, div_self hne]; ring
        _ = _ := by ring
    rw [key, ih, add_mul, pow_add, pow_add]
    ring
end Formalism.IncomingBounds
