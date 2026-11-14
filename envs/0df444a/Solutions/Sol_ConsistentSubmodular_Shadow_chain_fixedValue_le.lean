-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.chain_fixedValue_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:36.905261+00:00
-- url     : https://prove2.me/submissions/f990ad57-0f50-4db4-9f13-a1d86bface1b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

theorem sum_Iic_val {N : ℕ} (f : ℕ → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i ∈ Finset.range (j + 1), f i := by
  have h := Finset.sum_map (Finset.Iic j) Fin.valEmbedding f
  rw [Fin.map_valEmbedding_Iic] at h
  have hI : (Finset.Iic (j : ℕ)) = Finset.range (j + 1) := by
    ext x
    simp
  rw [hI] at h
  simpa using h.symm

section

variable {N : ℕ} {d : ℕ → ℝ}

theorem chainLeft_mono (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ N + 1) : chainLeft d i ≤ chainLeft d j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) fun k hk _ =>
    (chain_pos hd hN (by have := Finset.mem_range.mp hk; omega)).le

end

end ConsistentSubmodular.Shadow

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow
variable {N : ℕ} {d : ℕ → ℝ}
variable (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1)

theorem solution :
    (chainInstance N d hd hN).fixedValue ≤
      ∑ j : Fin (N + 1), chainProb d j * chainLeft d j + 1 := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hi := i.isLt
  have hdi := chain_pos hd hN (show (i : ℕ) ≤ N by omega)
  have hpoint : ∀ j : Fin (N + 1),
      chainProb d j * (chainInstance N d hd hN).value i j ≤
        chainProb d j * chainLeft d j + (if j ≤ i then chainProb d j * d i else 0) := by
    intro j
    have hp := chainProb_nonneg hd hN (show (j : ℕ) ≤ N by have := j.isLt; omega)
    simp only [chainInstance, IntervalInstance.value, mul_add]
    refine add_le_add le_rfl ?_
    split_ifs with hji
    · refine mul_le_mul_of_nonneg_left (max_le hdi.le ?_) hp
      linarith [le_max_left (chainLeft d i) (chainLeft d j)]
    · have hlt : (i : ℕ) + 1 ≤ j := by
        have := Fin.lt_def.mp (not_le.mp hji)
        omega
      have hmono := chainLeft_mono hd hN hlt (by have := j.isLt; omega)
      rw [chainLeft, Finset.sum_range_succ, ← chainLeft] at hmono
      rw [max_eq_left (by linarith [le_max_right (chainLeft d i) (chainLeft d j)]), mul_zero]
  calc _ ≤ ∑ j : Fin (N + 1), (chainProb d j * chainLeft d j +
          (if j ≤ i then chainProb d j * d i else 0)) := Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ j : Fin (N + 1), chainProb d j * chainLeft d j + 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_ge_eq_Iic,
        ← Finset.sum_mul, sum_Iic_val (chainProb d) i, sum_chainProb, one_div_mul_cancel hdi.ne']

end
