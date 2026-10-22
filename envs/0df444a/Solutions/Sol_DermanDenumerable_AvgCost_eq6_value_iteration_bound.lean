-- Prove2me | solution 1 for DermanDenumerable.AvgCost.eq6_value_iteration_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:34:26.18147+00:00
-- url     : https://prove2.me/submissions/6e902f5f-5f9f-4808-800d-98b6c9a78ccc

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model

set_option autoImplicit false
open Filter SennottDP.AvgFinite DermanDenumerable.AvgCost

section aux
variable {S Act : Type} [Countable S] (M : MDC S Act) (i : S) (a : Act)

lemma dz_ne_top (j : S) : M.P i a j ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (by rw [M.P_sum]; exact ENNReal.one_ne_top) j

lemma dz_summable : Summable (fun j => (M.P i a j).toReal) :=
  ENNReal.summable_toReal (by rw [M.P_sum]; exact ENNReal.one_ne_top)

lemma dz_tsum : ∑' j, (M.P i a j).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (dz_ne_top M i a), M.P_sum]; simp

lemma dz_summ_bdd (u : S → ℝ) (K : ℝ) (hu : ∀ j, |u j| ≤ K) :
    Summable (fun j => (M.P i a j).toReal * u j) := by
  refine Summable.of_norm_bounded ((dz_summable M i a).mul_right K) (fun j => ?_)
  rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hu j) ENNReal.toReal_nonneg

lemma dz_mono (u u' : S → ℝ) (K : ℝ) (hu : ∀ j, |u j| ≤ K) (hu' : ∀ j, |u' j| ≤ K)
    (h : ∀ j, u j ≤ u' j) : expNext M i a u ≤ expNext M i a u' := by
  unfold expNext
  exact Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (h j) ENNReal.toReal_nonneg)
    (dz_summ_bdd M i a u K hu) (dz_summ_bdd M i a u' K hu')

lemma dz_shift (v : S → ℝ) (K c : ℝ) (hv : ∀ j, |v j| ≤ K) :
    expNext M i a (fun j => v j + c) = expNext M i a v + c := by
  unfold expNext
  have h1 := dz_summ_bdd M i a v K hv
  have h2 : Summable (fun j => (M.P i a j).toReal * c) := (dz_summable M i a).mul_right c
  have : (fun j => (M.P i a j).toReal * (v j + c)) = fun j => (M.P i a j).toReal * v j + (M.P i a j).toReal * c := by
    funext j; ring
  rw [this, Summable.tsum_add h1 h2, tsum_mul_right, dz_tsum]
  ring

end aux

theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (g : ℝ) (v : S → ℝ) (hv : BddFun v)
    (h1 : IsACOE M w g v) :
    ∃ C : ℝ, ∀ (n : ℕ) (i : S),
      (n : ℝ) * g + v i - C ≤ valueIter M w n i ∧ valueIter M w n i ≤ (n : ℝ) * g + v i + C := by
  obtain ⟨B, hBw⟩ := hB
  obtain ⟨Bv, hBv⟩ := hv
  refine ⟨B + Bv, ?_⟩
  intro n
  induction n with
  | zero =>
    intro i
    have e : valueIter M w 0 i = (M.A i).inf' (M.A_nonempty i) (w i) := rfl
    rw [e]
    obtain ⟨a0, ha0⟩ := M.A_nonempty i
    have hw0 := abs_le.1 (hBw i a0 ha0)
    have hv0 := abs_le.1 (hBv i)
    constructor
    · have : v i - (B + Bv) ≤ -B := by linarith
      simp only [Nat.cast_zero, zero_mul, zero_add]
      refine le_trans this (Finset.le_inf' _ _ (fun a ha => ?_))
      have := abs_le.1 (hBw i a ha)
      linarith
    · simp only [Nat.cast_zero, zero_mul, zero_add]
      refine le_trans (Finset.inf'_le _ ha0) ?_
      linarith
  | succ n ih =>
    intro i
    set u := valueIter M w n with hu
    have e : valueIter M w (n+1) i = (M.A i).inf' (M.A_nonempty i)
        (fun a => w i a + expNext M i a u) := rfl
    rw [e]
    set K : ℝ := Bv + |(n:ℝ) * g| + |B + Bv| with hK
    have hng1 := neg_abs_le ((n:ℝ) * g)
    have hng2 := le_abs_self ((n:ℝ) * g)
    have hC1 := neg_abs_le (B + Bv)
    have hC2 := le_abs_self (B + Bv)
    have hbu : ∀ j, |u j| ≤ K := fun j => by
      have := ih j
      have := abs_le.1 (hBv j)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hbp : ∀ j, |v j + ((n:ℝ) * g + (B + Bv))| ≤ K := fun j => by
      have := abs_le.1 (hBv j)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hbm : ∀ j, |v j + ((n:ℝ) * g - (B + Bv))| ≤ K := fun j => by
      have := abs_le.1 (hBv j)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hbv : ∀ j, |v j| ≤ K := fun j => by
      have := abs_le.1 (hBv j)
      have h0 : 0 ≤ |(n:ℝ) * g| := abs_nonneg _
      have h1' : 0 ≤ |B + Bv| := abs_nonneg _
      exact abs_le.2 ⟨by linarith, by linarith⟩
    constructor
    · refine Finset.le_inf' _ _ (fun a ha => ?_)
      have hup := (h1 i).2 a ha
      have hm := dz_mono M i a (fun j => v j + ((n:ℝ) * g - (B + Bv))) u K hbm hbu
        (fun j => by have := (ih j).1; linarith)
      have hs := dz_shift M i a v K ((n:ℝ) * g - (B + Bv)) hbv
      push_cast
      linarith
    · obtain ⟨a0, ha0, hEq⟩ := (h1 i).1
      refine le_trans (Finset.inf'_le _ ha0) ?_
      have hm := dz_mono M i a0 u (fun j => v j + ((n:ℝ) * g + (B + Bv))) K hbu hbp
        (fun j => by have := (ih j).2; linarith)
      have hs := dz_shift M i a0 v K ((n:ℝ) * g + (B + Bv)) hbv
      push_cast
      linarith
