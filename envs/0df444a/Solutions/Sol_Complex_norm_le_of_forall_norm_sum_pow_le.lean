-- Prove2me | solution 1 for Complex.norm_le_of_forall_norm_sum_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:54:56.271481+00:00
-- url     : https://prove2.me/submissions/6319f94a-6c99-4f17-9d9e-307e30bd8729

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace
import Theorems.Thm_Complex_exists_forall_norm_pow_sub_one_lt

namespace Complex
end Complex
namespace Filter
end Filter
namespace Finset
end Finset
namespace Topology
end Topology


/-!
# Bounding the terms of a family from bounds on its power sums

If `ω : ι → ℂ` is a finite family of complex numbers whose power sums satisfy
`‖∑ i, ω i ^ k‖ ≤ C * B ^ k` for every `k > 0`, then every `ω i` satisfies `‖ω i‖ ≤ B`.

This is the standard "no cancellation in the long run" argument: writing `M` for the largest
modulus occurring in the family and `S` for the set of indices attaining it, the numbers
`ω i / M` for `i ∈ S` lie on the unit circle, so by compactness of the torus there are
arbitrarily large exponents `n` for which all the `(ω i / M) ^ n`, `i ∈ S`, are simultaneously
close to `1`.  For such `n` the maximal terms of `∑ i, ω i ^ n` add up essentially without
cancellation, forcing `M ^ n ≲ C * B ^ n`, which is impossible for large `n` unless `M ≤ B`.
-/
set_option autoImplicit false
open Finset Filter Topology
open Complex

theorem solution {ι : Type*} [Fintype ι] {ω : ι → ℂ} {B C : ℝ}
    (hB : 0 < B) (h : ∀ k : ℕ, 0 < k → ‖∑ i, ω i ^ k‖ ≤ C * B ^ k) (i : ι) :
    ‖ω i‖ ≤ B := by
  classical
  have hne : (univ : Finset ι).Nonempty := ⟨i, mem_univ i⟩
  set M : ℝ := univ.sup' hne (fun j => ‖ω j‖) with hMdef
  have hiM : ‖ω i‖ ≤ M := le_sup' (fun j => ‖ω j‖) (mem_univ i)
  refine hiM.trans ?_
  by_contra hcon
  rw [not_le] at hcon
  have hM0 : 0 < M := hB.trans hcon
  -- the indices attaining the maximal modulus
  set S : Finset ι := {j ∈ univ | ‖ω j‖ = M} with hS
  have hSne : S.Nonempty := by
    obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' hne (fun j => ‖ω j‖)
    refine ⟨j, ?_⟩
    simp only [hS, mem_filter, mem_univ, true_and]
    rw [hMdef]
    exact hj.symm
  -- the second largest modulus (or `0`)
  set M' : ℝ := univ.sup' hne (fun j => if ‖ω j‖ = M then 0 else ‖ω j‖) with hM'def
  have hM'0 : 0 ≤ M' := by
    obtain ⟨j, hj⟩ := hne
    refine le_trans ?_ (le_sup' (fun j => if ‖ω j‖ = M then 0 else ‖ω j‖) hj)
    positivity
  have hM'M : M' < M := by
    refine (sup'_lt_iff hne).2 fun j _ => ?_
    by_cases hj : ‖ω j‖ = M
    · simpa [hj] using hM0
    · simp only [hj, if_false]
      exact lt_of_le_of_ne (le_sup' (fun j => ‖ω j‖) (mem_univ j)) hj
  have hle' : ∀ j ∉ S, ‖ω j‖ ≤ M' := by
    intro j hj
    have hj' : ‖ω j‖ ≠ M := by simpa [hS] using hj
    simpa [hj'] using le_sup' (fun j => if ‖ω j‖ = M then 0 else ‖ω j‖) (mem_univ j)
  -- the unit vectors carrying the maximal terms
  set u : ι → ℂ := fun j => if ‖ω j‖ = M then ω j / M else 1 with hu
  have huM : ∀ j, ‖u j‖ = 1 := by
    intro j
    by_cases hj : ‖ω j‖ = M
    · simp only [hu, hj, if_true]
      rw [norm_div, hj]
      simp [hM0.ne', abs_of_pos hM0]
    · simp [hu, hj]
  have hωu : ∀ j ∈ S, ω j = (M : ℂ) * u j := by
    intro j hj
    have hj' : ‖ω j‖ = M := by simpa [hS] using hj
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    simp only [hu, hj', if_true]
    field_simp
  set n₀ : ℕ := Fintype.card ι with hn₀
  have hn₀0 : 0 < (n₀ : ℝ) := by
    have : 0 < n₀ := Fintype.card_pos_iff.2 ⟨i⟩
    exact_mod_cast this
  set ε : ℝ := 1 / (2 * n₀) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    positivity
  -- large exponents kill both error terms
  have hBM : B / M < 1 := (div_lt_one hM0).2 hcon
  have hM'M1 : M' / M < 1 := (div_lt_one hM0).2 hM'M
  have hlim1 : Tendsto (fun n : ℕ => C * (B / M) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0:ℝ) ≤ B / M) hBM
    simpa using this.const_mul C
  have hlim2 : Tendsto (fun n : ℕ => (n₀ : ℝ) * (M' / M) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0:ℝ) ≤ M' / M) hM'M1
    simpa using this.const_mul (n₀ : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop,
      C * (B / M) ^ n < 1 / 4 ∧ (n₀ : ℝ) * (M' / M) ^ n < 1 / 4 :=
    (hlim1.eventually (gt_mem_nhds (by norm_num))).and
      (hlim2.eventually (gt_mem_nhds (by norm_num)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨n, hnN, hn0, hnu⟩ := exists_forall_norm_pow_sub_one_lt huM hε N
  obtain ⟨h1, h2⟩ := hN n hnN
  -- lower bound for the maximal part
  have hMn : (0:ℝ) < M ^ n := pow_pos hM0 n
  have hmain : ‖∑ j ∈ S, u j ^ n‖ ≥ 1 / 2 := by
    have hcard : (1:ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.card_ne_zero.2 hSne)
    have hsplit : ∑ j ∈ S, u j ^ n = (S.card : ℂ) + ∑ j ∈ S, (u j ^ n - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    have herr : ‖∑ j ∈ S, (u j ^ n - 1)‖ ≤ 1 / 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ S, ‖u j ^ n - 1‖ ≤ ∑ _j ∈ S, ε :=
            Finset.sum_le_sum fun j _ => (hnu j).le
        _ = (S.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n₀ : ℝ) * ε := by
            gcongr
            exact Finset.card_le_univ S
        _ = 1 / 2 := by
            rw [hεdef]
            field_simp
    have hnormcard : ‖(S.card : ℂ)‖ = (S.card : ℝ) := by
      simp
    have hh := norm_sub_le ((S.card : ℂ) + ∑ j ∈ S, (u j ^ n - 1)) (∑ j ∈ S, (u j ^ n - 1))
    rw [add_sub_cancel_right, hnormcard] at hh
    rw [hsplit]
    linarith
  -- split the power sum into its maximal and its smaller part
  have hsplit2 : ∑ j, ω j ^ n = (M : ℂ) ^ n * (∑ j ∈ S, u j ^ n) + ∑ j ∈ Sᶜ, ω j ^ n := by
    rw [← Finset.sum_add_sum_compl S (fun j => ω j ^ n)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hωu j hj, mul_pow]
  have hMcast : ‖((M : ℂ)) ^ n‖ = M ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0]
  have hbig : M ^ n * (1 / 2) ≤ ‖(M : ℂ) ^ n * (∑ j ∈ S, u j ^ n)‖ := by
    rw [norm_mul, hMcast]
    exact mul_le_mul_of_nonneg_left hmain hMn.le
  have hsmall : ‖∑ j ∈ Sᶜ, ω j ^ n‖ ≤ (n₀ : ℝ) * M' ^ n := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Sᶜ, ‖ω j ^ n‖ ≤ ∑ _j ∈ Sᶜ, M' ^ n := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hle' j (Finset.mem_compl.1 hj)) n
      _ = (Sᶜ.card : ℝ) * M' ^ n := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n₀ : ℝ) * M' ^ n := by
          gcongr
          exact Finset.card_le_univ _
  -- the maximal part dominates, contradicting the hypothesis for large `n`
  have hlow : M ^ n * (1 / 2) - (n₀ : ℝ) * M' ^ n ≤ ‖∑ j, ω j ^ n‖ := by
    have := norm_sub_le ((M : ℂ) ^ n * (∑ j ∈ S, u j ^ n) + ∑ j ∈ Sᶜ, ω j ^ n)
      (∑ j ∈ Sᶜ, ω j ^ n)
    rw [add_sub_cancel_right] at this
    rw [hsplit2]
    linarith
  have hMn' : (M : ℝ) ^ n ≠ 0 := hMn.ne'
  have e1 : C * B ^ n = M ^ n * (C * (B / M) ^ n) := by
    rw [div_pow]
    field_simp
  have e2 : (n₀ : ℝ) * M' ^ n = M ^ n * ((n₀ : ℝ) * (M' / M) ^ n) := by
    rw [div_pow]
    field_simp
  have hfin : M ^ n * (1 / 2) ≤ M ^ n * (C * (B / M) ^ n) + M ^ n * ((n₀ : ℝ) * (M' / M) ^ n) := by
    have hup := h n hn0
    rw [← e1, ← e2]
    linarith
  nlinarith [mul_lt_mul_of_pos_left h1 hMn, mul_lt_mul_of_pos_left h2 hMn]
