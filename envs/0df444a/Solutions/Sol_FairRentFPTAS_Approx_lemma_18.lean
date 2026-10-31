-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:47:31.771826+00:00
-- url     : https://prove2.me/submissions/c671bc9e-717e-4f21-b350-9a7785ae2453

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_lemma_16

open FairRentFPTAS.Approx

theorem solution {n : ℕ} (W : Fin n → Fin n → ℝ) (hW : ∀ a r, 0 ≤ W a r)
    (hpos : ∃ π : Equiv.Perm (Fin n), ∀ a, 0 < W a (π a)) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℝ), (∀ r, 0 < d r) ∧
      ∀ a r, d r * W a r ≤ d (σ a) * W a (σ a) := by
  classical
  obtain ⟨π, hπ⟩ := hpos
  set w : Fin n → Fin n → ℝ := fun a r => Real.log (W a r) with hw
  set S : ℝ := ∑ a, ∑ r, |w a r| with hS
  have hS0 : 0 ≤ S := by positivity
  set B : Fin n → Fin n → ℝ := fun a r => if 0 < W a r then w a r else -(2 * S + 1) with hB
  have hwS : ∀ a r, |w a r| ≤ ∑ r', |w a r'| := fun a r =>
    Finset.single_le_sum (f := fun r' => |w a r'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)
  -- lower bound for permutations using only positive edges
  have hlow : ∀ τ : Equiv.Perm (Fin n), (∀ a, 0 < W a (τ a)) → -S ≤ ∑ a, B a (τ a) := by
    intro τ hτ
    have e : ∑ a, B a (τ a) = ∑ a, w a (τ a) := by
      apply Finset.sum_congr rfl; intro a _; simp only [hB, if_pos (hτ a)]
    rw [e]
    have h1 : ∑ a, -|w a (τ a)| ≤ ∑ a, w a (τ a) := Finset.sum_le_sum (fun a _ => neg_abs_le _)
    have h2 : ∑ a, |w a (τ a)| ≤ S := Finset.sum_le_sum (fun a _ => hwS a (τ a))
    rw [Finset.sum_neg_distrib] at h1
    linarith
  -- upper bound for permutations using a zero edge
  have hup : ∀ τ : Equiv.Perm (Fin n), (∃ a, ¬ 0 < W a (τ a)) → ∑ a, B a (τ a) ≤ -S - 1 := by
    rintro τ ⟨a0, ha0⟩
    have h1 : ∀ a, B a (τ a) + (if 0 < W a (τ a) then 0 else 2 * S + 1) ≤ ∑ r', |w a r'| := by
      intro a
      by_cases h : 0 < W a (τ a)
      · simp only [hB, if_pos h, add_zero]; exact le_trans (le_abs_self _) (hwS a _)
      · simp only [hB, if_neg h]
        linarith [Finset.sum_nonneg (fun r' (_ : r' ∈ Finset.univ) => abs_nonneg (w a r'))]
    have h2 := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h1 a)
    rw [Finset.sum_add_distrib] at h2
    have h3 : 2 * S + 1 ≤ ∑ a, (if 0 < W a (τ a) then (0 : ℝ) else 2 * S + 1) := by
      have := Finset.single_le_sum (f := fun a => if 0 < W a (τ a) then (0 : ℝ) else 2 * S + 1)
        (fun a _ => by split_ifs <;> linarith) (Finset.mem_univ a0)
      simp only [if_neg ha0] at this
      exact this
    linarith
  -- a maximum-weight permutation for `B`
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun τ => ∑ a, B a (τ a)) ⟨1, Finset.mem_univ _⟩
  have hσpos : ∀ a, 0 < W a (σ a) := by
    by_contra hc
    push_neg at hc
    obtain ⟨a0, ha0⟩ := hc
    have h1 := hup σ ⟨a0, not_lt.mpr ha0⟩
    have h2 := hlow π hπ
    have h3 := hσ π (Finset.mem_univ _)
    linarith
  obtain ⟨u, hu⟩ := (lemma_16 B σ).mpr (fun τ => hσ τ (Finset.mem_univ _))
  refine ⟨σ, fun r => Real.exp (-u r), fun r => Real.exp_pos _, ?_⟩
  intro a r
  by_cases hr : 0 < W a r
  · have h := hu a r
    simp only [hB, if_pos hr, if_pos (hσpos a)] at h
    have h' := Real.exp_le_exp.mpr h
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hr, Real.exp_log (hσpos a)] at h'
    show Real.exp (-u r) * W a r ≤ Real.exp (-u (σ a)) * W a (σ a)
    rw [Real.exp_neg, Real.exp_neg]
    rw [div_eq_mul_inv, div_eq_mul_inv] at h'
    linarith
  · have : W a r = 0 := le_antisymm (not_lt.mp hr) (hW a r)
    show Real.exp (-u r) * W a r ≤ Real.exp (-u (σ a)) * W a (σ a)
    rw [this, mul_zero]
    exact (mul_pos (Real.exp_pos _) (hσpos a)).le
