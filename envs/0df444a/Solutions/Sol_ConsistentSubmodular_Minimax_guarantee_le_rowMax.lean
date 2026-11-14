-- Prove2me | solution 1 for ConsistentSubmodular.Minimax.guarantee_le_rowMax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:03.725763+00:00
-- url     : https://prove2.me/submissions/c87a8ed0-35ac-4994-a4bd-61c4d32d3171

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

theorem guarantee_le (w : Fin (m + 1) → Fin (m + 1) → ℝ) (a : Point m) (j : Fin (m + 1)) :
    guarantee w a ≤ ∑ i, a i * w i j :=
  Finset.inf'_le _ (Finset.mem_univ j)

end ConsistentSubmodular.Minimax

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Minimax
variable {m : ℕ}

theorem solution (w : Fin (m + 1) → Fin (m + 1) → ℝ) {a b : Point m}
    (ha : IsSimplex a) (hb : IsSimplex b) : guarantee w a ≤ rowMax w b := by
  calc guarantee w a = ∑ j, b j * guarantee w a := by rw [← Finset.sum_mul, hb.2, one_mul]
    _ ≤ ∑ j, b j * ∑ i, a i * w i j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (guarantee_le w a j) (hb.1 j)
    _ = ∑ i, a i * ∑ j, b j * w i j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, a i * rowMax w b :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i => ∑ j, b j * w i j) (Finset.mem_univ i)) (ha.1 i)
    _ = rowMax w b := by rw [← Finset.sum_mul, ha.2, one_mul]

end
