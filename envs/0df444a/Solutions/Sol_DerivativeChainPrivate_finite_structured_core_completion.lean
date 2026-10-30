-- Prove2me | solution 1 for DerivativeChainPrivate.finite_structured_core_completion
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:12:27.569425+00:00
-- url     : https://prove2.me/submissions/d022da9c-4a69-45e6-9cc2-8add7cfcc718

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


open DerivativeChainPrivate in
theorem solution {Ω : Type*} [Fintype Ω]
    (π length : Ω → ℝ) (X : ℕ → Ω → ℂ) (s : ℕ) (u : ℂ)
    (hπ : ∀ ω, 0 ≤ π ω) (htotal : ∑ ω, π ω = 1)
    (horth : ∀ k < s, ∑ ω, π ω *
      ((X k ω - u).re * (X (k + 1) ω - X k ω).re +
        (X k ω - u).im * (X (k + 1) ω - X k ω).im) = 0)
    (hmean_re : ∑ ω, π ω * (X s ω).re = u.re)
    (hmean_im : ∑ ω, π ω * (X s ω).im = u.im)
    (hdisk : ∀ ω, 0 < π ω → Complex.normSq (X s ω) ≤ 1)
    (hpoint : ∀ ω, 0 < π ω → length ω ^ 2 ≤ ((s : ℝ) + 1) *
      (Complex.normSq (X 0 ω - u) +
        ∑ k ∈ Finset.range s, Complex.normSq (X (k + 1) ω - X k ω))) :
    ∃ ω, 0 < π ω ∧
      length ω ≤ Real.sqrt (((s : ℝ) + 1) * (1 - Complex.normSq u)) := by
  classical
  let C (z w : ℂ) : ℝ := (z - u).re * (w - z).re + (z - u).im * (w - z).im
  have hnorm (z w : ℂ) : Complex.normSq (w - u) = Complex.normSq (z - u) +
      Complex.normSq (w - z) + 2 * C z w := by
    dsimp [C]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hid : ∀ n : ℕ,
      (∀ k < n, ∑ ω, π ω * C (X k ω) (X (k + 1) ω) = 0) →
      (∑ ω, π ω * (Complex.normSq (X 0 ω - u) +
        ∑ k ∈ Finset.range n, Complex.normSq (X (k + 1) ω - X k ω))) =
        ∑ ω, π ω * Complex.normSq (X n ω - u) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := ih (fun k hk => hn k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hl := hn n (Nat.lt_succ_self n)
      simp only [Finset.sum_range_succ]
      calc
        _ = (∑ ω, π ω * (Complex.normSq (X 0 ω - u) +
              ∑ k ∈ Finset.range n, Complex.normSq (X (k + 1) ω - X k ω))) +
            ∑ ω, π ω * Complex.normSq (X (n + 1) ω - X n ω) := by
          simp only [← add_assoc, mul_add, Finset.sum_add_distrib]
        _ = (∑ ω, π ω * Complex.normSq (X n ω - u)) +
            ∑ ω, π ω * Complex.normSq (X (n + 1) ω - X n ω) := by rw [hp]
        _ = ∑ ω, π ω * Complex.normSq (X (n + 1) ω - u) := by
          have hh : (∑ ω, π ω * Complex.normSq (X (n + 1) ω - u)) =
              (∑ ω, π ω * Complex.normSq (X n ω - u)) +
              (∑ ω, π ω * Complex.normSq (X (n + 1) ω - X n ω)) +
              2 * (∑ ω, π ω * C (X n ω) (X (n + 1) ω)) := by
            calc
              _ = ∑ ω, (π ω * Complex.normSq (X n ω - u) +
                  π ω * Complex.normSq (X (n + 1) ω - X n ω) +
                  2 * (π ω * C (X n ω) (X (n + 1) ω))) := by
                apply Finset.sum_congr rfl
                intro ω _
                rw [hnorm (X n ω) (X (n + 1) ω)]
                ring
              _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hl, mul_zero, add_zero] at hh
          exact hh.symm
  have hv : (∑ ω, π ω * Complex.normSq (X s ω - u)) =
      (∑ ω, π ω * Complex.normSq (X s ω)) - Complex.normSq u := by
    calc
      _ = ∑ ω, (π ω * Complex.normSq (X s ω) -
          2 * u.re * (π ω * (X s ω).re) -
          2 * u.im * (π ω * (X s ω).im) + Complex.normSq u * π ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hmean_re, hmean_im, htotal, mul_one, Complex.normSq_apply]
        ring
  have hsecond : (∑ ω, π ω * Complex.normSq (X s ω)) ≤ 1 := by
    calc
      _ ≤ ∑ ω, π ω := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hp : 0 < π ω
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdisk ω hp) (hπ ω)
        · have hz : π ω = 0 := le_antisymm (le_of_not_gt hp) (hπ ω)
          simp [hz]
      _ = 1 := htotal
  let E (ω : Ω) : ℝ := Complex.normSq (X 0 ω - u) +
    ∑ k ∈ Finset.range s, Complex.normSq (X (k + 1) ω - X k ω)
  have he : (∑ ω, π ω * E ω) ≤ 1 - Complex.normSq u := by
    change (∑ ω, π ω * (Complex.normSq (X 0 ω - u) +
      ∑ k ∈ Finset.range s, Complex.normSq (X (k + 1) ω - X k ω))) ≤ _
    rw [hid s horth, hv]
    linarith
  have hselect : ∀ (f : Ω → ℝ) (c : ℝ), (∑ ω, π ω * f ω ≤ c) →
      ∃ ω, 0 < π ω ∧ f ω ≤ c := by
    intro f c haverage
    by_contra h
    push Not at h
    have hexists : ∃ ω, 0 < π ω := by
      by_contra hh
      push Not at hh
      have hsum : ∑ ω, π ω ≤ 0 := Finset.sum_nonpos (by
        intro ω _
        exact hh ω)
      linarith
    obtain ⟨ω₀, hω₀⟩ := hexists
    have hweak : ∀ ω ∈ Finset.univ, π ω * c ≤ π ω * f ω := by
      intro ω _
      by_cases hp : 0 < π ω
      · exact mul_le_mul_of_nonneg_left (le_of_lt (h ω hp)) (hπ ω)
      · have hz : π ω = 0 := le_antisymm (le_of_not_gt hp) (hπ ω)
        simp [hz]
    have hstrict : (∑ ω, π ω * c) < ∑ ω, π ω * f ω := by
      apply Finset.sum_lt_sum hweak
      exact ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (h ω₀ hω₀) hω₀⟩
    have hconst : (∑ ω, π ω * c) = c := by
      rw [← Finset.sum_mul, htotal, one_mul]
    rw [hconst] at hstrict
    exact (not_lt_of_ge haverage) hstrict
  obtain ⟨ω, hω, heω⟩ := hselect E (1 - Complex.normSq u) he
  have hsq : length ω ^ 2 ≤ ((s : ℝ) + 1) * (1 - Complex.normSq u) :=
    (hpoint ω hω).trans (mul_le_mul_of_nonneg_left heω (by positivity))
  exact ⟨ω, hω, Real.le_sqrt_of_sq_le hsq⟩
