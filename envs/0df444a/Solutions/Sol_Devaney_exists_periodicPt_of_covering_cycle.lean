-- Prove2me | solution 1 for Devaney.exists_periodicPt_of_covering_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:49:17.76347+00:00
-- url     : https://prove2.me/submissions/901f9290-1cb5-44db-9094-b69d4d928a7e

import Mathlib
import Definitions.Def_Devaney_sarkovskii
import Theorems.Thm_Devaney_exists_subinterval_image_eq
import Theorems.Thm_Devaney_exists_fixedPoint_of_covers_self

open Set Function

namespace Shk

def Cov (f : ℝ → ℝ) (a b c d : ℝ) : Prop := uIcc c d ⊆ f '' uIcc a b

theorem exists_fixed_of_cov_self {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : Cov f a b a b) : ∃ z ∈ uIcc a b, f z = z := by
  have hI : uIcc a b = Icc (min a b) (max a b) := rfl
  have hle : min a b ≤ max a b := min_le_max
  have h' : Devaney.Covers f (Icc (min a b) (max a b)) (Icc (min a b) (max a b)) := by
    rw [← hI]; exact h
  obtain ⟨z, hz, hfz⟩ :=
    Devaney.exists_fixedPoint_of_covers_self f hf (min a b) (max a b) hle h'
  exact ⟨z, by rw [hI]; exact hz, hfz⟩

theorem exists_exact_subinterval {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : Cov f a b c d) :
    ∃ u v : ℝ, uIcc u v ⊆ uIcc a b ∧ f '' uIcc u v = uIcc c d :=
  Devaney.exists_subinterval_image_eq f hf a b c d h

/-- Backward construction along a chain of coverings: there is a closed interval inside
`[A 0, B 0]` whose `k+1`-st image is exactly `[c,d]`, and whose `i`-th image stays inside
`[A i, B i]`. -/
theorem chain_pre {f : ℝ → ℝ} (hf : Continuous f) (A B : ℕ → ℝ) :
    ∀ (k : ℕ) (c d : ℝ), (∀ i < k, Cov f (A i) (B i) (A (i+1)) (B (i+1))) →
      Cov f (A k) (B k) c d →
      ∃ u v : ℝ, f^[k+1] '' uIcc u v = uIcc c d ∧
        ∀ i ≤ k, f^[i] '' uIcc u v ⊆ uIcc (A i) (B i) := by
  intro k
  induction k with
  | zero =>
      intro c d _ hcov
      obtain ⟨u, v, h1, h2⟩ := exists_exact_subinterval hf hcov
      refine ⟨u, v, by simpa using h2, ?_⟩
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa using h1
  | succ k ih =>
      intro c d hchain hcov
      obtain ⟨u', v', h1, h2⟩ := exists_exact_subinterval hf hcov
      have hcov' : Cov f (A k) (B k) u' v' := h1.trans (hchain k (by omega))
      obtain ⟨u, v, e1, e2⟩ := ih u' v' (fun i hi => hchain i (by omega)) hcov'
      refine ⟨u, v, ?_, ?_⟩
      · rw [Function.iterate_succ', Set.image_comp, e1, h2]
      · intro i hi
        rcases Nat.lt_or_ge i (k+1) with h | h
        · exact e2 i (by omega)
        · have hik : i = k + 1 := by omega
          subst hik
          rw [e1]; exact h1

/-- **Loop lemma.**  A cycle of closed intervals `[A 0,B 0] → [A 1,B 1] → ⋯ → [A n,B n] =
[A 0,B 0]` contains a point `y` with `f^[n] y = y` which follows the loop. -/
theorem exists_loop_point {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (hn : 0 < n)
    (A B : ℕ → ℝ) (hcov : ∀ i < n, Cov f (A i) (B i) (A (i+1)) (B (i+1)))
    (hA : A n = A 0) (hB : B n = B 0) :
    ∃ y, f^[n] y = y ∧ ∀ i < n, f^[i] y ∈ uIcc (A i) (B i) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨u, v, e1, e2⟩ := chain_pre hf A B k (A 0) (B 0) (fun i hi => hcov i (by omega))
    (by rw [← hA, ← hB]; exact hcov k (by omega))
  have hK : uIcc u v ⊆ uIcc (A 0) (B 0) := by simpa using e2 0 (by omega)
  have hself : Cov (f^[k+1]) u v u v := by
    show uIcc u v ⊆ f^[k+1] '' uIcc u v
    rw [e1]; exact hK
  obtain ⟨y, hy, hfy⟩ := exists_fixed_of_cov_self (hf.iterate (k+1)) hself
  exact ⟨y, hfy, fun i hi => e2 i (by omega) ⟨y, hy, rfl⟩⟩

end Shk

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ)
    (hcov : ∀ i < n, Devaney.Covers f (Set.uIcc (a i) (b i))
      (Set.uIcc (a (i + 1)) (b (i + 1))))
    (ha : a n = a 0) (hb : b n = b 0) :
    ∃ y : ℝ, f^[n] y = y ∧ ∀ i < n, f^[i] y ∈ Set.uIcc (a i) (b i) :=
  Shk.exists_loop_point hf n hn a b hcov ha hb
