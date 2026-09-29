-- Prove2me | solution 1 for Freiman.form_orbit_transport_induction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:20:18.056468+00:00
-- url     : https://prove2.me/submissions/8251732f-a68a-4a6b-8096-0a543918081f

import Definitions.Def_Freiman_reducedForms

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem minimum_step (α β γ δ : ℝ) (a : ℤ)
    (h : ∀ p q : ℤ, reducedValue α β (a * p + q) p = -reducedValue γ δ p q) :
    reducedMinimum α β = reducedMinimum γ δ := by
  unfold reducedMinimum quadraticMinimum
  congr 1
  ext v
  change (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ v = |reducedValue α β p q|) ↔
    (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ v = |reducedValue γ δ p q|)
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨q, p - a * q, ?_, ?_⟩
    · by_cases hq : q = 0
      · right
        simp only [hq, mul_zero, sub_zero]
        exact hpq.resolve_right (fun hn => hn hq)
      · exact Or.inl hq
    · have he := h q (p - a * q)
      have hi : a * q + (p - a * q) = p := by ring
      rw [hi] at he
      rw [he, abs_neg]
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨a * p + q, p, ?_, ?_⟩
    · by_cases hp : p = 0
      · left
        simp only [hp, mul_zero, zero_add]
        exact hpq.resolve_left (fun hn => hn hp)
      · exact Or.inr hp
    · rw [h, abs_neg]

theorem solution (R : ReducedOrbit)
    (hstep : ∀ n p q : ℤ,
      reducedValue (R.alpha n) (R.beta n) (((R.digits n : ℕ) : ℤ) * p + q) p =
        -reducedValue (R.alpha (n + 1)) (R.beta (n + 1)) p q) :
    ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n) =
      reducedMinimum (R.alpha 0) (R.beta 0) := by
  have hs (n : ℤ) : reducedMinimum (R.alpha n) (R.beta n) =
      reducedMinimum (R.alpha (n + 1)) (R.beta (n + 1)) := by
    apply minimum_step (R.alpha n) (R.beta n) (R.alpha (n + 1)) (R.beta (n + 1))
      ((R.digits n : ℕ) : ℤ)
    intro p q
    exact hstep n p q
  intro n
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih => exact (hs n).symm.trans ih
  | pred n ih =>
    have hp := hs (-(n : ℤ) - 1)
    rw [sub_add_cancel] at hp
    exact hp.trans ih
