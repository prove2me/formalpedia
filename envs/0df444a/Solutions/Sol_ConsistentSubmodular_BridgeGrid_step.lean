-- Prove2me | solution 1 for ConsistentSubmodular.BridgeGrid.step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:56.959961+00:00
-- url     : https://prove2.me/submissions/26e52983-74bd-4ced-8053-33d5e0ee5553

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeGrid

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

theorem typeL1_simplex_le_two {p q : Point m} (hp : IsSimplex p) (hq : IsSimplex q) :
    typeL1 p q ≤ 2 := by
  calc
    typeL1 p q ≤ ∑ i, (p i + q i) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_le.mpr ⟨by linarith [hp.1 i, hq.1 i], by linarith [hp.1 i, hq.1 i]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num

theorem typeL1_mix (p q : Point m) (x y : ℝ) :
    typeL1 (mix p q x) (mix p q y) = |x - y| * typeL1 p q := by
  unfold typeL1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : mix p q x i - mix p q y i = (x - y) * (q i - p i) := by unfold mix; ring
  rw [he, abs_mul, abs_sub_comm (q i)]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.BridgeGrid
variable {n : ℕ}

theorem solution (K : ℕ) (hK : 0 < K) (j : Fin K) :
    typeL1 (point K j.castSucc) (point K j.succ) ≤ 2 / K := by
  rw [point, point, typeL1_mix]
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have he : |((j.castSucc.val : ℕ) : ℝ) / K - ((j.succ.val : ℕ) : ℝ) / K| = 1 / K := by
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have he : (j.val : ℝ) / K - ((j.val : ℝ) + 1) / K = -(1 / K) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  rw [he]
  have h := mul_le_mul_of_nonneg_left
    (typeL1_simplex_le_two (simplex_vertex (0 : Fin 2)) (simplex_vertex (1 : Fin 2)))
    (show (0 : ℝ) ≤ 1 / K by positivity)
  rw [show (2 : ℝ) / K = 1 / K * 2 by ring]
  exact h

end
