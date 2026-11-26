-- Prove2me | solution 1 for Erdos287.finite_local_residue_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:51:22.645623+00:00
-- url     : https://prove2.me/submissions/3fc3905d-e2d5-46d2-950d-033c5ac5204e

import Mathlib

open Finset

set_option autoImplicit false

private theorem sum_restrictions {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (q : Finset ι) (E : (q → κ) → ℝ) :
    (∑ a : ι → κ, (Fintype.card κ : ℝ) ^ q.card * E (fun i => a i)) =
      (Fintype.card κ : ℝ) ^ Fintype.card ι * ∑ b : q → κ, E b := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun i => i ∈ q) (fun _ => κ)
  have hsplit :
      (∑ a : ι → κ, E (fun i => a i)) =
        ∑ f : (q → κ) × ({i : ι // i ∉ q} → κ), E f.1 :=
    Fintype.sum_equiv split _ _ (fun _ => rfl)
  have hcard : Fintype.card ({i : ι // i ∉ q} → κ) =
      Fintype.card κ ^ (qᶜ : Finset ι).card := by
    rw [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_compl]
  rw [← Finset.mul_sum, hsplit, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, nsmul_eq_mul, hcard, Nat.cast_pow]
  rw [← Finset.mul_sum, ← mul_assoc, ← pow_add, Finset.card_add_card_compl]

/-- A uniform global estimate controls the sum over all finite local choices. -/
theorem solution (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (Q : Finset (Finset ι)) (E : (q : Finset ι) → (q → κ) → ℝ)
    (G : Finset ι → ℝ) (B : ℝ)
    (hE : ∀ q ∈ Q, ∀ b : q → κ, 0 ≤ E q b ∧ E q b ≤ G q)
    (hB : ∀ a : ι → κ, (∑ q ∈ Q, E q (fun i => a i)) ≤ B) :
    (∑ q ∈ Q, ∑ b : q → κ, E q b) ≤ Real.sqrt B *
      Real.sqrt (∑ q ∈ Q, ((Fintype.card κ : ℝ) ^ q.card) ^ 2 * G q) := by
  classical
  let w (q : Finset ι) := (Fintype.card κ : ℝ) ^ q.card
  let H := Real.sqrt B * Real.sqrt (∑ q ∈ Q, (w q) ^ 2 * G q)
  have hweighted (a : ι → κ) : (∑ q ∈ Q, w q * E q (fun i => a i)) ≤ H := by
    let F (q : Finset ι) := E q (fun i => a i)
    have hF (q : Finset ι) (hq : q ∈ Q) : 0 ≤ F q ∧ F q ≤ G q := hE q hq _
    have heq : (∑ q ∈ Q, w q * F q) =
        ∑ q ∈ Q, Real.sqrt (F q) * (w q * Real.sqrt (F q)) := by
      apply sum_congr rfl
      intro q hq
      calc
        w q * F q = w q * (Real.sqrt (F q)) ^ 2 := by rw [Real.sq_sqrt (hF q hq).1]
        _ = _ := by ring
    rw [heq]
    refine (Real.sum_mul_le_sqrt_mul_sqrt Q (fun q => Real.sqrt (F q))
      (fun q => w q * Real.sqrt (F q))).trans ?_
    have h₁ : (∑ q ∈ Q, (Real.sqrt (F q)) ^ 2) ≤ B := by
      have hh : (∑ q ∈ Q, (Real.sqrt (F q)) ^ 2) = ∑ q ∈ Q, F q :=
        sum_congr rfl (fun q hq => Real.sq_sqrt (hF q hq).1)
      rw [hh]
      exact hB a
    have h₂ : (∑ q ∈ Q, (w q * Real.sqrt (F q)) ^ 2) ≤ ∑ q ∈ Q, (w q) ^ 2 * G q := by
      apply sum_le_sum
      intro q hq
      rw [mul_pow, Real.sq_sqrt (hF q hq).1]
      exact mul_le_mul_of_nonneg_left (hF q hq).2 (sq_nonneg _)
    exact mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum :
      (∑ a : ι → κ, ∑ q ∈ Q, w q * E q (fun i => a i)) =
        (Fintype.card κ : ℝ) ^ Fintype.card ι * ∑ q ∈ Q, ∑ b : q → κ, E q b := by
    rw [sum_comm, Finset.mul_sum]
    exact sum_congr rfl (fun q _ => sum_restrictions q (E q))
  have htotal := sum_le_sum (s := (univ : Finset (ι → κ))) (fun a _ => hweighted a)
  rw [hsum, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow] at htotal
  have hcard : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast Fintype.card_pos (α := κ)
  exact (le_of_mul_le_mul_left htotal (pow_pos hcard _))

