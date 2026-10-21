-- Prove2me | solution 1 for CoProdBundle.Equil.feasible_pred
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:46:05.440287+00:00
-- url     : https://prove2.me/submissions/2b87ed04-50c5-4fe7-907b-122c1bdea82c

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

set_option autoImplicit false
open CoProdBundle.Equil

lemma psum_zero {I : ℕ} (c : Fin I → ℝ) : psum c 0 = 0 := by
  simp [psum]

lemma psum_succ {I : ℕ} (c : Fin I → ℝ) (k : ℕ) (h : k < I) :
    psum c (k+1) = psum c k + c ⟨k, h⟩ := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin I => (j:ℕ) < k+1) =
      insert ⟨k,h⟩ (Finset.univ.filter (fun j : Fin I => (j:ℕ) < k)) := by
    ext j; simp [Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring

theorem solution (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    Feasible c θ 1 ∧ ∀ k : ℕ, 2 ≤ k → Feasible c θ k → Feasible c θ (k - 1) := by
  constructor
  · refine ⟨le_refl _, by simpa using hI, ?_⟩
    have h1 : psum c 1 = c ⟨0, hI⟩ := by
      rw [psum_succ c 0 hI, psum_zero]; simp
    show c ⟨0, hI⟩ ≤ psum c 1 / (((1:ℕ):ℝ) - alpha θ)
    rw [h1]
    have : (((1:ℕ):ℝ) - alpha θ) = 3 * θ / 2 := by unfold alpha; push_cast; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [hc0 ⟨0, hI⟩]
  · intro k hk hf
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    obtain ⟨_, h, hle⟩ := hf
    have hn1 : n + 1 < I := by simpa using h
    have hn : n < I := by omega
    have hps : psum c (n+2) = psum c (n+1) + c ⟨n+1, hn1⟩ := psum_succ c (n+1) hn1
    have hps1 : psum c (n+1) = psum c n + c ⟨n, hn⟩ := psum_succ c n hn
    refine ⟨by omega, by simpa using hn, ?_⟩
    have hmono : c ⟨n, hn⟩ ≤ c ⟨n+1, hn1⟩ := hcm (by simp [Fin.le_def])
    have e1 : (⟨n + 2 - 1 - 1, by omega⟩ : Fin I) = ⟨n, hn⟩ := rfl
    have hle' : c ⟨n+1, hn1⟩ ≤ psum c (n+2) / (((n+2:ℕ):ℝ) - alpha θ) := hle
    show c ⟨n, hn⟩ ≤ psum c (n+1) / (((n+1:ℕ):ℝ) - alpha θ)
    have hα : alpha θ < 1 := by unfold alpha; linarith
    have hd : (0:ℝ) < ((n+2:ℕ):ℝ) - alpha θ := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hd1 : (0:ℝ) < ((n+1:ℕ):ℝ) - alpha θ := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [le_div_iff₀ hd] at hle'
    rw [le_div_iff₀ hd1]
    rw [hps] at hle'
    push_cast at hle' hd hd1 ⊢
    have := hc0 ⟨n+1, hn1⟩
    nlinarith [mul_le_mul_of_nonneg_right hmono hd1.le]
