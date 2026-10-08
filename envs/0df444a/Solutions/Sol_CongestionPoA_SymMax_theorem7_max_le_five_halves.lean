-- Prove2me | solution 1 for CongestionPoA.SymMax.theorem7_max_le_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:41:44.750561+00:00
-- url     : https://prove2.me/submissions/ebe7f4c3-ab24-4c06-a07e-f78129109f6f

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

set_option autoImplicit false

namespace CongestionPoA.SymMax

theorem af6_sum_mem_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (P : ι → Finset E) (g : E → ℝ) :
    ∑ j, ∑ e ∈ P j, g e = ∑ e, (load P e : ℝ) * g e := by
  calc ∑ j, ∑ e ∈ P j, g e = ∑ j, ∑ e, (if e ∈ P j then g e else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ e, ∑ j, (if e ∈ P j then g e else 0) := Finset.sum_comm
    _ = ∑ e, (load P e : ℝ) * g e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl

theorem af6_load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc (Finset.univ.filter (fun k => e ∈ Function.update A i S k)).card
      ≤ (insert i (Finset.univ.filter (fun k => e ∈ A k))).card := by
        apply Finset.card_le_card
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        by_cases hki : k = i
        · simp [hki]
        · rw [Function.update_of_ne hki] at hk
          simp [hk]
    _ ≤ _ := Finset.card_insert_le _ _

theorem af6_nat_ineq (α β : ℕ) : (3 : ℝ) * (β * (α + 1)) ≤ α ^ 2 + 5 * β ^ 2 := by
  have key : (3 : ℤ) * (β * (α + 1)) ≤ α ^ 2 + 5 * β ^ 2 := by
    rcases Nat.lt_or_ge β 2 with h | h
    · interval_cases β
      · push_cast; nlinarith [sq_nonneg (α : ℤ)]
      · have : ((α : ℤ) - 1) * ((α : ℤ) - 2) ≥ 0 := by
          rcases Nat.lt_or_ge α 2 with h2 | h2
          · interval_cases α <;> norm_num
          · have : (2 : ℤ) ≤ α := by exact_mod_cast h2
            nlinarith
        push_cast; nlinarith
    · have : (2 : ℤ) ≤ β := by exact_mod_cast h
      nlinarith [sq_nonneg (2 * (α : ℤ) - 3 * β)]
  exact_mod_cast key

end CongestionPoA.SymMax

open CongestionPoA.SymMax in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    maxCost G A ≤ 5 / 2 * maxCost G P := by
  obtain ⟨a, b, ha, hb, hf⟩ := hlin
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (cost G A)
  have hmaxA : maxCost G A = cost G A i := hi
  set c := cost G A i with hc
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  -- Nash bound for each j
  set h : E → ℝ := fun e => a e * ((load A e : ℝ) + 1) + b e with hh
  have hj : ∀ j, c ≤ ∑ e ∈ P j, h e := by
    intro j
    have hS : P j ∈ G.strategies i := by rw [hsym i j]; exact hP j
    have h1 := hA.2 i (P j) hS
    refine h1.trans ?_
    simp only [cost, Function.update_self]
    refine Finset.sum_le_sum (fun e _ => ?_)
    rw [hf, hh]
    have := af6_load_update_le A i (P j) e
    have : ((load (Function.update A i (P j)) e : ℕ) : ℝ) ≤ (load A e : ℝ) + 1 := by
      exact_mod_cast this
    nlinarith [ha e]
  have hsum : N * c ≤ ∑ e, (load P e : ℝ) * h e := by
    rw [← af6_sum_mem_eq]
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN] using this
  have hsumA : sumCost G A = ∑ e, (load A e : ℝ) * (a e * load A e + b e) := by
    unfold sumCost cost
    rw [af6_sum_mem_eq A (fun e => G.latency e (load A e))]
    simp [hf]
  have hsumP : sumCost G P = ∑ e, (load P e : ℝ) * (a e * load P e + b e) := by
    unfold sumCost cost
    rw [af6_sum_mem_eq P (fun e => G.latency e (load P e))]
    simp [hf]
  have hSA : sumCost G A ≤ N * c := by
    unfold sumCost
    have : ∀ k ∈ (Finset.univ : Finset ι), cost G A k ≤ c := by
      intro k _
      rw [← hmaxA]
      exact Finset.le_sup' (cost G A) (Finset.mem_univ k)
    have := Finset.sum_le_sum this
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN] using this
  have hSP : sumCost G P ≤ N * maxCost G P := by
    unfold sumCost
    have : ∀ k ∈ (Finset.univ : Finset ι), cost G P k ≤ maxCost G P := by
      intro k _
      exact Finset.le_sup' (cost G P) (Finset.mem_univ k)
    have := Finset.sum_le_sum this
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN] using this
  have hpt : ∑ e, (load P e : ℝ) * h e ≤ sumCost G A / 3 + 5 / 3 * sumCost G P := by
    rw [hsumA, hsumP, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have k1 := af6_nat_ineq (load A e) (load P e)
    have hα : (0 : ℝ) ≤ load A e := Nat.cast_nonneg _
    have hβ : (0 : ℝ) ≤ load P e := Nat.cast_nonneg _
    rw [hh]
    nlinarith [mul_le_mul_of_nonneg_left k1 (ha e), mul_nonneg (hb e) hα, mul_nonneg (hb e) hβ]
  rw [hmaxA]
  have : N * c ≤ N * c / 3 + 5 / 3 * (N * maxCost G P) := by linarith
  have h2 : N * c ≤ N * (5 / 2 * maxCost G P) := by linarith
  exact le_of_mul_le_mul_left h2 hNpos
