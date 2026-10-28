-- Prove2me | solution 1 for CompositeLB.DetLip.avgF_hard_min
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:44:37.845528+00:00
-- url     : https://prove2.me/submissions/8ccfb981-79fe-4452-96df-c7371a48d68d

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

open CompositeLB.DetLip in
theorem solution {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : Fin m → ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (hb : b = 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    let f : Fin m → E d → ℝ := fun i => hardF b k v (δ i)
    let xb : E d := b • ∑ r ∈ Finset.range (k + 1), v r
    (∀ x : E d,
      avgF f x = 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
        (((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ))) *
          ∑ r ∈ Finset.Icc 1 k,
            |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|) ∧
    (∀ x : E d, 0 ≤ avgF f x) ∧ avgF f xb = 0 ∧ ‖xb‖ = 1 := by
  intro f xb
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact this.ne'
  have hform : ∀ x : E d,
      avgF f x = 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
        (((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ))) *
          ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| := by
    intro x
    unfold avgF
    simp only [f, hardF]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
    have e : ∑ r ∈ Finset.Icc 1 k, ∑ i : Fin m,
        δ i r * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|
        = ∑ r ∈ Finset.Icc 1 k, ((m / 2 : ℕ) : ℝ) * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [← Finset.sum_mul, hsum r hr]
    rw [e, ← Finset.mul_sum]
    field_simp
  have hinner : ∀ r, r ≤ k → inner ℝ xb (v r) = b := by
    intro r hr
    simp only [xb]
    rw [inner_smul_left, sum_inner, Finset.sum_range (fun s => inner ℝ (v s) (v r))]
    have : ∑ s : Fin (k + 1), inner ℝ (v s) (v r) = 1 := by
      have h := fun s => (orthonormal_iff_ite.mp hv) s ⟨r, by omega⟩
      simp only at h
      rw [Finset.sum_congr rfl fun s _ => h s, Finset.sum_ite_eq']
      simp
    rw [this]
    simp
  refine ⟨hform, fun x => ?_, ?_, ?_⟩
  · rw [hform]
    have : 0 ≤ ((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ)) := by positivity
    have : 0 ≤ ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| :=
      Finset.sum_nonneg fun r _ => abs_nonneg _
    positivity
  · rw [hform, hinner 0 (by omega), sub_self, abs_zero, mul_zero, zero_add]
    have : ∑ r ∈ Finset.Icc 1 k, |inner ℝ xb (v (r - 1)) - inner ℝ xb (v r)| = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr' := Finset.mem_Icc.mp hr
      rw [hinner (r - 1) (by omega), hinner r hr'.2, sub_self, abs_zero]
    rw [this, mul_zero]
  · have hb2 : b ^ 2 * ((k : ℝ) + 1) = 1 := by
      rw [hb, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      push_cast
      field_simp
    have hsq : ‖xb‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [show xb = b • ∑ r ∈ Finset.range (k + 1), v r from rfl]
      rw [inner_smul_right, inner_sum]
      rw [Finset.sum_congr rfl fun r hr => hinner r (by have := Finset.mem_range.mp hr; omega)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      linarith [hb2]
    have h0 := norm_nonneg xb
    nlinarith
