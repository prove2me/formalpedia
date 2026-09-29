-- Prove2me | solution 1 for Diaz.power_support_sumfree
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:53.155433+00:00
-- url     : https://prove2.me/submissions/c519833e-ebf0-4c52-bfae-57ba9465be77

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution (S : Set ℤ)
    (hsym : ∀ n : ℤ, n ∈ S → -n ∈ S)
    (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
    (hpair : ∀ d : ℤ, d ≠ 0 → ∀ n₁ n₂ n₃ : ℤ, n₁ ≠ n₂ → n₁ ≠ n₃ → n₂ ≠ n₃ →
        n₁ ∈ S → n₁ + d ∈ S → n₂ ∈ S → n₂ + d ∈ S → n₃ ∈ S → n₃ + d ∈ S → False) :
    (∀ m n : ℤ, m ≠ 0 → n ≠ 0 → m + n ≠ 0 → m ∈ S → n ∈ S → m + n ∉ S)
      ∧ (2 : ℤ) ∉ S ∧ (-2 : ℤ) ∉ S ∧ (3 : ℤ) ∉ S ∧ (-3 : ℤ) ∉ S := by
  have sumfree : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 → m + n ≠ 0 → m ∈ S → n ∈ S → m + n ∉ S := by
    intro m n hm hn hmn hmS hnS hsum
    refine hpair m hm (-m) 0 n (by omega) (by omega) (by omega)
      (hsym m hmS) (by simpa using h0) h0 (by simpa using hmS) hnS ?_
    rw [show n + m = m + n by ring]; exact hsum
  have h2 : (2 : ℤ) ∉ S := by
    have := sumfree 1 1 (by norm_num) (by norm_num) (by norm_num) h1 h1
    simpa using this
  have h2' : (-2 : ℤ) ∉ S := fun hc => h2 (by simpa using hsym (-2) hc)
  have h3 : (3 : ℤ) ∉ S := by
    intro hc
    have hm1 : (-1 : ℤ) ∈ S := by simpa using hsym 1 h1
    have hm3 : (-3 : ℤ) ∈ S := by simpa using hsym 3 hc
    exact hpair 2 (by norm_num) (-3) (-1) 1 (by norm_num) (by norm_num) (by norm_num)
      hm3 (by norm_num; exact hm1) hm1 (by norm_num; exact h1) h1 (by norm_num; exact hc)
  have h3' : (-3 : ℤ) ∉ S := fun hc => h3 (by simpa using hsym (-3) hc)
  exact ⟨sumfree, h2, h2', h3, h3'⟩
