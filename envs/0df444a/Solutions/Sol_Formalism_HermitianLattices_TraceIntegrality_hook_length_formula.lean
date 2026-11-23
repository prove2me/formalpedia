-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.hook_length_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:29.743871+00:00
-- url     : https://prove2.me/submissions/3366bea3-317b-4f89-a0f5-ddb0ed9f5d31

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HookRowProductEqFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma shifted_product_telescoping (a M : ℕ) : ∀ c, c ≤ a →
    (∏ j ∈ range c, (a - j + M + 1)) * (a - c + M + 1) = (a + M + 1) * ∏ j ∈ range c, (a - j + M)
  | 0, _ => by simp
  | c + 1, h => by
    rw [prod_range_succ, prod_range_succ]
    have ih := shifted_product_telescoping a M c (by omega)
    have e : a - (c + 1) + M + 1 = a - c + M := by omega
    rw [e]
    calc _ = ((∏ j ∈ range c, (a - j + M + 1)) * (a - c + M + 1)) * (a - c + M) := by ring
      _ = _ := by rw [ih]; ring
private lemma hook_row_product_eq_factorial (a : ℕ) (μ : ℕ → ℕ) : ∀ M, (∀ k l, k ≤ l → l < M → μ l ≤ μ k) →
    (∀ k, k < M → μ k ≤ a) →
    (∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0))
      * ∏ k ∈ range M, (a - μ k + k + 1) = (a + M).factorial
  | 0, _, _ => by
    simp only [range_zero, sum_empty, prod_empty, add_zero, mul_one]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.1 hj
    omega
  | M + 1, hanti, hle => by
    have ih := hook_row_product_eq_factorial a μ M (fun k l hkl hl => hanti k l hkl (by omega)) (fun k hk => hle k (by omega))
    have hc : μ M ≤ a := hle M (by omega)
    have key : (∏ j ∈ range a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0))
        * (a - μ M + M + 1)
        = (a + M + 1) * ∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by
      rw [← prod_range_mul_prod_Ico _ hc, ← prod_range_mul_prod_Ico _ hc]
      have h1 : ∏ j ∈ range (μ M), (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0)
          = ∏ j ∈ range (μ M), (a - j + M + 1) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_range.1 hj
        have : ∑ k ∈ range (M + 1), (if j < μ k then 1 else 0) = ∑ k ∈ range (M + 1), 1 := by
          refine sum_congr rfl fun k hk => ?_
          have hk' := mem_range.1 hk
          have := hanti k M (by omega) (by omega)
          rw [if_pos (by omega)]
        rw [this]; simp; ring
      have h2 : ∏ j ∈ range (μ M), (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0)
          = ∏ j ∈ range (μ M), (a - j + M) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_range.1 hj
        have : ∑ k ∈ range M, (if j < μ k then 1 else 0) = ∑ k ∈ range M, 1 := by
          refine sum_congr rfl fun k hk => ?_
          have hk' := mem_range.1 hk
          have := hanti k M (by omega) (by omega)
          rw [if_pos (by omega)]
        rw [this]; simp
      have h3 : ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0)
          = ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by
        refine prod_congr rfl fun j hj => ?_
        have hj' := mem_Ico.1 hj
        rw [sum_range_succ, if_neg (by omega), add_zero]
      rw [h1, h2, h3]
      have ht := shifted_product_telescoping a M (μ M) hc
      calc _ = ((∏ j ∈ range (μ M), (a - j + M + 1)) * (a - μ M + M + 1))
              * ∏ j ∈ Ico (μ M) a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0) := by ring
        _ = _ := by rw [ht]; ring
    rw [prod_range_succ (fun k => a - μ k + k + 1)]
    calc _ = ((∏ j ∈ range a, (a - j + ∑ k ∈ range (M + 1), if j < μ k then 1 else 0))
              * (a - μ M + M + 1)) * ∏ k ∈ range M, (a - μ k + k + 1) := by ring
      _ = (a + M + 1) * ((∏ j ∈ range a, (a - j + ∑ k ∈ range M, if j < μ k then 1 else 0))
              * ∏ k ∈ range M, (a - μ k + k + 1)) := by rw [key]; ring
      _ = _ := by rw [ih, ← add_assoc, Nat.factorial_succ]
private lemma prod_filter_gt_eq_prod_range {α : Type} [CommMonoid α] {N : ℕ} (i : Fin N) (g : ℕ → α) :
    ∏ j ∈ (univ : Finset (Fin N)).filter (fun j => i < j), g j
      = ∏ k ∈ range (N - (i + 1)), g (i + 1 + k) := by
  rw [prod_filter]
  have h1 : ∏ j : Fin N, (if i < j then g j else 1)
      = ∏ n ∈ range N, (if (i : ℕ) < n then g n else 1) :=
    Fin.prod_univ_eq_prod_range (fun n => if (i : ℕ) < n then g n else 1) N
  rw [h1, ← prod_range_mul_prod_Ico _ (show (i : ℕ) + 1 ≤ N from i.2), prod_Ico_eq_prod_range]
  rw [prod_eq_one, one_mul]
  · refine prod_congr rfl fun k _ => ?_
    rw [if_pos]; omega
  · intro n hn
    have := mem_range.1 hn
    rw [if_neg]; omega
private lemma sum_filter_gt_eq_sum_range {N : ℕ} (i : Fin N) (g : ℕ → ℕ) :
    ∑ j ∈ (univ : Finset (Fin N)).filter (fun j => i < j), g j
      = ∑ k ∈ range (N - (i + 1)), g (i + 1 + k) := by
  rw [sum_filter]
  have h1 : ∑ j : Fin N, (if i < j then g j else 0)
      = ∑ n ∈ range N, (if (i : ℕ) < n then g n else 0) :=
    Fin.sum_univ_eq_sum_range (fun n => if (i : ℕ) < n then g n else 0) N
  rw [h1, ← sum_range_add_sum_Ico _ (show (i : ℕ) + 1 ≤ N from i.2), sum_Ico_eq_sum_range]
  rw [sum_eq_zero, zero_add]
  · refine sum_congr rfl fun k _ => ?_
    rw [if_pos]; omega
  · intro n hn
    have := mem_range.1 hn
    rw [if_neg]; omega
private lemma hook_row_identity_fin {N : ℕ} (nu : Fin N → ℕ) (h : Antitone nu) (i : Fin N) :
    (∏ j ∈ range (nu i), hookLen nu i j)
      * ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ)))
      = (nu i + N - 1 - i).factorial := by
  set ν' : ℕ → ℕ := fun n => if hn : n < N then nu ⟨n, hn⟩ else 0 with hν'
  have hv : ∀ j : Fin N, ν' j = nu j := fun j => by simp [hν']
  have hanti : ∀ p q, p ≤ q → q < N → ν' q ≤ ν' p := by
    intro p q hpq hq
    have hp : p < N := by omega
    simp only [hν', dif_pos hp, dif_pos hq]
    exact h (by simpa using hpq)
  have e1 : ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ)))
      = ∏ k ∈ range (N - (i + 1)), (nu i - ν' (i + 1 + k) + k + 1) := by
    have := prod_filter_gt_eq_prod_range i (fun n => nu i - ν' n + (n - (i : ℕ)))
    simp only [hv] at this
    rw [this]
    refine prod_congr rfl fun k _ => ?_
    omega
  have e2 : ∀ j, hookLen nu i j
      = nu i - j + ∑ k ∈ range (N - (i + 1)), if j < ν' (i + 1 + k) then 1 else 0 := by
    intro j
    unfold hookLen
    rw [← filter_filter, card_filter]
    have := sum_filter_gt_eq_sum_range i (fun n => if j < ν' n then 1 else 0)
    simp only [hv] at this
    rw [this]
  rw [e1, prod_congr rfl (fun j _ => e2 j)]
  have := hook_row_product_eq_factorial (nu i) (fun k => ν' (i + 1 + k)) (N - (i + 1))
    (fun k l hkl hl => hanti _ _ (by omega) (by omega))
    (fun k hk => by
      have := hanti i (i + 1 + k) (by omega) (by omega)
      rwa [hv] at this)
  rw [this]
  congr 1
  have := i.2
  omega
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : HookLengthFormula := by
  intro N nu h
  have hden : ∀ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)
      = ((∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ))) : ℕ) : ℝ) := by
    intro i
    rw [Nat.cast_prod]
    refine prod_congr rfl fun j hj => ?_
    have hij : i < j := (mem_filter.1 hj).2
    have h1 : nu j ≤ nu i := h hij.le
    have h2 : (i : ℕ) ≤ j := hij.le
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  have hpos : ∀ i : Fin N,
      0 < ∏ j ∈ univ.filter (fun j => i < j), (nu i - nu j + ((j : ℕ) - (i : ℕ))) := by
    intro i
    refine prod_pos fun j hj => ?_
    have hij : (i : ℕ) < j := (mem_filter.1 hj).2
    omega
  unfold hookF
  rw [eq_div_iff]
  · rw [prod_congr rfl (fun i _ => hden i)]
    unfold hookProd
    rw [Nat.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, hook_row_identity_fin nu h i]
  · rw [prod_congr rfl (fun i _ => hden i)]
    refine prod_ne_zero_iff.2 fun i _ => ?_
    exact_mod_cast (hpos i).ne'
end Formalism.HermitianLattices.TraceIntegrality
