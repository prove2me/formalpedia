-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_determinant_and_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:40:30.51041+00:00
-- url     : https://prove2.me/submissions/0c06b7d6-0319-4bae-8f35-422b3ae0c0a4

import Mathlib
set_option autoImplicit false

namespace EulerPadeWork

lemma determinant (P Q : ℕ → ℤ)
    (h0 : Q 0 * P 1 - Q 1 * P 0 = 1)
    (hP : ∀ n : ℕ, P (n+2) = (2*(n:ℤ)+4)*P (n+1) - ((n:ℤ)+1)^2*P n)
    (hQ : ∀ n : ℕ, Q (n+2) = (2*(n:ℤ)+4)*Q (n+1) - ((n:ℤ)+1)^2*Q n)
    (n : ℕ) : Q n * P (n+1) - Q (n+1) * P n = (n.factorial : ℤ)^2 := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [hP n, hQ n]
    calc
      Q (n+1) * ((2*(n:ℤ)+4)*P (n+1) - ((n:ℤ)+1)^2*P n) -
          ((2*(n:ℤ)+4)*Q (n+1) - ((n:ℤ)+1)^2*Q n) * P (n+1) =
          ((n:ℤ)+1)^2*(Q n * P (n+1) - Q (n+1) * P n) := by ring
      _ = (((n+1).factorial : ℕ) : ℤ)^2 := by
        rw [ih, Nat.factorial_succ]
        push_cast
        ring

lemma adjacent_nonzero (P Q : ℕ → ℤ) (n : ℕ)
    (h : Q n * P (n+1) - Q (n+1) * P n = (n.factorial : ℤ)^2) (a : ℝ) :
    (Q n : ℝ)*a - (P n : ℝ) ≠ 0 ∨
      (Q (n+1) : ℝ)*a - (P (n+1) : ℝ) ≠ 0 := by
  by_contra hh
  push Not at hh
  have hr : (Q n : ℝ) * (P (n+1) : ℝ) - (Q (n+1) : ℝ) * (P n : ℝ) =
      (n.factorial : ℝ)^2 := by exact_mod_cast h
  have hn : (n.factorial : ℝ)^2 ≠ 0 := by positivity
  apply hn
  linear_combination -(Q n : ℝ) * hh.2 + (Q (n+1) : ℝ) * hh.1 - hr

end EulerPadeWork


theorem solution (P Q : ℕ → ℤ)
    (h0 : Q 0 * P 1 - Q 1 * P 0 = 1)
    (hP : ∀ n : ℕ, P (n+2) = (2*(n:ℤ)+4)*P (n+1) - ((n:ℤ)+1)^2*P n)
    (hQ : ∀ n : ℕ, Q (n+2) = (2*(n:ℤ)+4)*Q (n+1) - ((n:ℤ)+1)^2*Q n) :
    ∀ n : ℕ,
      Q n * P (n+1) - Q (n+1) * P n = (n.factorial : ℤ)^2 ∧
      ∀ a : ℝ, (Q n : ℝ)*a - (P n : ℝ) ≠ 0 ∨
        (Q (n+1) : ℝ)*a - (P (n+1) : ℝ) ≠ 0 := by
  intro n
  have h := EulerPadeWork.determinant P Q h0 hP hQ n
  exact ⟨h, fun a => EulerPadeWork.adjacent_nonzero P Q n h a⟩

#print axioms solution
