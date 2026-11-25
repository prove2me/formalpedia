-- Prove2me | solution 1 for Formalism.IncomingBounds.expSeriesAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:30.121849+00:00
-- url     : https://prove2.me/submissions/108675a8-18cb-43b4-a7ea-1895d4db5641

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_coeff_pow_mul_pow_eq_zero
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_coeff_mvExp
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_degree_le_of_mem_antidiagonal
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_choose_div_factorial

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : ExpAdd := by
  intro K _ _ σ a b ha hb
  classical
  ext m
  have hN : m.degree < m.degree + 1 := Nat.lt_succ_self _
  set N := m.degree + 1 with hNdef
  have hab : constantCoeff (a + b) = 0 := by simp [ha, hb]
  have hmid : ∀ F : ℕ → ℕ → K,
      ∑ k ∈ range N, ∑ j ∈ range (k + 1), F j (k - j) =
        ∑ j ∈ range N, ∑ j' ∈ range (N - j), F j j' := by
    intro F
    rw [Finset.sum_comm' (t' := range N) (s' := fun j => Ico j N)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      congr 1
      omega
    · intro k j
      simp only [mem_range, mem_Ico]
      omega
  calc coeff m (mvExp (a + b))
      = ∑ k ∈ range N, coeff m ((a + b) ^ k) / (k.factorial : K) := thmPExp_coeff_mvExp hab m hN
    _ = ∑ k ∈ range N, ∑ j ∈ range (k + 1),
          coeff m (a ^ j * b ^ (k - j)) / ((j.factorial : K) * ((k - j).factorial : K)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [add_pow, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [mem_range] at hj
        rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C, mul_div_assoc,
          thmPExp_choose_div_factorial (by omega), mul_one_div]
    _ = ∑ j ∈ range N, ∑ j' ∈ range (N - j),
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) :=
        hmid (fun j j' => coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)))
    _ = ∑ j ∈ range N, ∑ j' ∈ range N,
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        apply Finset.sum_subset (range_subset_range.2 (by omega))
        intro j' _ hj'
        simp only [mem_range, not_lt] at hj'
        rw [thmPExp_coeff_pow_mul_pow_eq_zero ha hb (by omega), zero_div]
    _ = ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b) := by
        symm
        calc ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b)
            = ∑ pq ∈ antidiagonal m, ∑ j ∈ range N, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := by
              refine Finset.sum_congr rfl (fun pq hpq => ?_)
              rw [thmPExp_coeff_mvExp ha pq.1 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).1; omega),
                thmPExp_coeff_mvExp hb pq.2 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).2; omega),
                Finset.sum_mul_sum]
          _ = ∑ j ∈ range N, ∑ pq ∈ antidiagonal m, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun j' _ => ?_)
              rw [coeff_mul, Finset.sum_div]
              refine Finset.sum_congr rfl (fun pq _ => ?_)
              rw [div_mul_div_comm]
    _ = coeff m (mvExp a * mvExp b) := (coeff_mul _ _ _).symm
end Formalism.IncomingBounds
