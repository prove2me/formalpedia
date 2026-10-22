-- Prove2me | solution 1 for DIGing.Push.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:46:24.025881+00:00
-- url     : https://prove2.me/submissions/15616a1c-c074-4524-9b01-b82afda378c3

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

set_option autoImplicit false

open DIGing.Undir

lemma frob_le_add {n p : ℕ} (c : ℝ) (hc : 0 ≤ c) (a b1 b2 : Stack n p)
    (h : ∀ i, ‖a i‖ ≤ c * (‖b1 i‖ + ‖b2 i‖)) : frob a ≤ c * (frob b1 + frob b2) := by
  have key : ∀ v : Stack n p,
      frob v = ‖(WithLp.toLp 2 (fun i => ‖v i‖) : EuclideanSpace ℝ (Fin n))‖ := by
    intro v
    rw [EuclideanSpace.norm_eq]
    simp [frob]
  rw [key, key b1, key b2]
  have hle : ‖(WithLp.toLp 2 (fun i => ‖a i‖) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖c • ((WithLp.toLp 2 (fun i => ‖b1 i‖) : EuclideanSpace ℝ (Fin n)) +
        (WithLp.toLp 2 (fun i => ‖b2 i‖) : EuclideanSpace ℝ (Fin n)))‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  calc _ ≤ _ := hle
    _ = c * ‖(WithLp.toLp 2 (fun i => ‖b1 i‖) : EuclideanSpace ℝ (Fin n)) +
        (WithLp.toLp 2 (fun i => ‖b2 i‖) : EuclideanSpace ℝ (Fin n))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_add_le _ _) hc

theorem solution {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc : Fin n → ℝ)
    (h4 : Assumption4 f Lc) (x : ℕ → Stack n p) (xstar : EuclideanSpace ℝ (Fin p)) :
    ∀ K : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      ergK lam K (fun k => frob (zSeq f x k)) ≤
        Lmax Lc * (1 + 1 / lam) * ergK lam K (fun k => frob (x k - ones xstar)) := by
  intro K lam hl0 hl1
  have hEk : ∀ j ≤ K, frob (x j - ones xstar) / lam ^ j ≤ ergK lam K (fun k => frob (x k - ones xstar)) :=
    fun j hj => Finset.le_sup' (fun k => frob (x k - ones xstar) / lam ^ k)
      (Finset.mem_range.2 (by omega))
  set E := ergK lam K (fun k => frob (x k - ones xstar)) with hE
  have hE0 : 0 ≤ E := le_trans (div_nonneg (Real.sqrt_nonneg _) (by positivity)) (hEk 0 (Nat.zero_le _))
  have hL0 : 0 ≤ Lmax Lc := Real.iSup_nonneg (fun i => (h4 i).1.le)
  have hLi : ∀ i, Lc i ≤ Lmax Lc := fun i => le_ciSup (Finite.bddAbove_range _) i
  have hR0 : 0 ≤ Lmax Lc * (1 + 1 / lam) * E :=
    mul_nonneg (mul_nonneg hL0 (by positivity)) hE0
  unfold ergK
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ K := by
    have := Finset.mem_range.1 hk
    omega
  show frob (zSeq f x k) / lam ^ k ≤ _
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa [zSeq, frob] using hR0
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hz : frob (zSeq f x (j + 1)) ≤
        Lmax Lc * (frob (x (j + 1) - ones xstar) + frob (x j - ones xstar)) := by
      apply frob_le_add _ hL0
      intro i
      have e : zSeq f x (j + 1) i = gradient (f i) (x (j + 1) i) - gradient (f i) (x j i) := by
        simp [zSeq, gradStack]
      rw [e]
      calc ‖gradient (f i) (x (j + 1) i) - gradient (f i) (x j i)‖
          ≤ Lc i * ‖x (j + 1) i - x j i‖ := (h4 i).2.2 _ _
        _ ≤ Lmax Lc * (‖(x (j + 1) - (ones xstar : Stack n p)) i‖ + ‖(x j - (ones xstar : Stack n p)) i‖) := by
          have : ‖x (j + 1) i - x j i‖ ≤ ‖(x (j + 1) - (ones xstar : Stack n p)) i‖ + ‖(x j - (ones xstar : Stack n p)) i‖ := by
            calc ‖x (j + 1) i - x j i‖
                = ‖(x (j + 1) i - xstar) - (x j i - xstar)‖ := by congr 1; abel
              _ ≤ ‖x (j + 1) i - xstar‖ + ‖x j i - xstar‖ := norm_sub_le _ _
              _ = _ := by simp [ones]
          exact mul_le_mul (hLi i) this (norm_nonneg _) hL0
    have hA := hEk (j + 1) hk'
    have hB := hEk j (by omega)
    have hpos : (0 : ℝ) < lam ^ (j + 1) := by positivity
    have hB2 : frob (x j - ones xstar) / lam ^ (j + 1) ≤ E / lam := by
      rw [pow_succ, ← div_div]
      exact div_le_div_of_nonneg_right hB hl0.le
    calc frob (zSeq f x (j + 1)) / lam ^ (j + 1)
        ≤ Lmax Lc * (frob (x (j + 1) - ones xstar) + frob (x j - ones xstar)) / lam ^ (j + 1) :=
          div_le_div_of_nonneg_right hz hpos.le
      _ = Lmax Lc * (frob (x (j + 1) - ones xstar) / lam ^ (j + 1)
            + frob (x j - ones xstar) / lam ^ (j + 1)) := by ring
      _ ≤ Lmax Lc * (E + E / lam) := mul_le_mul_of_nonneg_left (add_le_add hA hB2) hL0
      _ = Lmax Lc * (1 + 1 / lam) * E := by ring
