-- Prove2me | solution 1 for CollatzFrontier.eventual_descent_iff_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:09:44.304922+00:00
-- url     : https://prove2.me/submissions/f2233b7b-dbde-492d-aa8e-af4b1937d6d2

import Definitions.Def_collatzFrontierCertificate
import Theorems.Thm_CollatzFrontier_chainCertificate_accepts
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open CollatzFrontier

namespace CollatzFrontierAux

/-! Helper lemmas, transcribed from `AffineStep.lean`, `FiniteCertificate.lean`,
`UniformDescent.lean`, and the completeness direction of `CertificateCompleteness.lean`
(research/executable-coverage-20261002 @ 3835de1, stacking on main @ 4d656b9). -/

/-- A power-of-two factor supplies an upper bound without fixing the valuation. -/
theorem syracuseStep_le_of_pow_two_factor {x y e : ℕ}
    (h : 3 * x + 1 = 2 ^ e * y) : syracuseStep x ≤ y := by
  unfold syracuseStep
  rw [h, Nat.ordCompl_self_pow_mul y e Nat.prime_two]
  exact Nat.ordCompl_le y 2

/-- Exact affine transfer; oddness is required only for an exact step. -/
theorem syracuseStep_affine (e : ℕ) {b A c D q : ℕ}
    (hc : 3 * b + 1 = 2 ^ e * c)
    (hD : 3 * A = 2 ^ e * D)
    (hodd : ¬ 2 ∣ c + D * q) :
    syracuseStep (b + A * q) = c + D * q := by
  unfold syracuseStep
  have h : 3 * (b + A * q) + 1 = 2 ^ e * (c + D * q) := by
    calc
      3 * (b + A * q) + 1 = (3 * b + 1) + (3 * A) * q := by ring
      _ = 2 ^ e * (c + D * q) := by rw [hc, hD]; ring
  rw [h]
  exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two hodd

/-- Finite row data imply an exact Syracuse step for every natural parameter. -/
theorem exactRowValid_sound {s : AffineState} {row : CertificateRow}
    (h : ExactRowValid s row) (q : ℕ) :
    syracuseStep (s.eval q) = row.next.eval q := by
  rcases h with ⟨_, hc, hA, hodd, heven⟩
  apply syracuseStep_affine row.exponent hc hA
  have hmod : (row.next.constant + row.next.coefficient * q) % 2 = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, hodd, heven]
  intro hdvd
  have hz := Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- The exact-prefix checker is sound for the full iterate, not just one input. -/
theorem runExactPrefix_sound (rows : List CertificateRow)
    (s result : AffineState) (h : runExactPrefix s rows = some result) (q : ℕ) :
    syracuseStep^[rows.length] (s.eval q) = result.eval q := by
  induction rows generalizing s with
  | nil =>
      simp only [runExactPrefix, Option.some.injEq] at h
      subst result
      rfl
  | cons row rest ih =>
      simp only [runExactPrefix] at h
      split at h
      next hrow =>
        rw [List.length_cons, Function.iterate_succ_apply,
          exactRowValid_sound hrow q]
        exact ih row.next h
      next hrow => contradiction

/-- The terminal row requires only divisibility, with no oddness condition. -/
theorem terminalRowValid_sound {s : AffineState} {row : CertificateRow}
    (h : TerminalRowValid s row) (q : ℕ) :
    syracuseStep (s.eval q) ≤ row.next.eval q := by
  rcases h with ⟨_, hc, hA⟩
  apply syracuseStep_le_of_pow_two_factor (e := row.exponent)
  dsimp [AffineState.eval]
  calc
    3 * (s.constant + s.coefficient * q) + 1 =
        (3 * s.constant + 1) + (3 * s.coefficient) * q := by ring
    _ = 2 ^ row.exponent * (row.next.constant + row.next.coefficient * q) := by
      rw [hc, hA]
      ring

/-- Acceptance certifies strict descent for every member of the progression. -/
theorem checkDescent_sound (cert : DescentCertificate)
    (h : checkDescent cert = true) (q : ℕ) :
    syracuseStep^[cert.exactRows.length + 1] (cert.start.eval q) < cert.start.eval q := by
  cases hrun : runExactPrefix cert.start cert.exactRows with
  | none => simp [checkDescent, hrun] at h
  | some last =>
      simp only [checkDescent, hrun, decide_eq_true_eq] at h
      rcases h with ⟨_, hterminal, hconstant, hcoefficient⟩
      have hexact := runExactPrefix_sound cert.exactRows cert.start last hrun q
      have hbound := terminalRowValid_sound hterminal q
      have hmul := Nat.mul_le_mul_right q hcoefficient
      have hgap : cert.terminal.next.eval q < cert.start.eval q := by
        dsimp [AffineState.eval]
        omega
      rw [Function.iterate_succ_apply', hexact]
      exact lt_of_le_of_lt hbound hgap

theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  apply Nat.odd_iff.mpr
  have hnot : ¬ 2 ∣ syracuseStep n :=
    Nat.not_dvd_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  have hne : syracuseStep n % 2 ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hlt := Nat.mod_lt (syracuseStep n) (show 0 < 2 by decide)
  omega

theorem syracuse_iterate_odd (n : ℕ) (hn : Odd n) (i : ℕ) :
    Odd (syracuseStep^[i] n) := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_odd _

/-- An actual finite descent is represented by an accepted canonical dyadic certificate.
The modulus is adaptive; its size is not asserted to be optimal. -/
theorem finite_descent_has_certificate (n t : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hdesc : syracuseStep^[t] n < n) :
    ∃ K : ℕ, ∃ cert : DescentCertificate,
      cert.start.constant = n ∧ cert.start.coefficient = 2 ^ K ∧
      cert.exactRows.length + 1 = t ∧
      cert.terminal.next.constant = syracuseStep^[t] n ∧ checkDescent cert = true := by
  cases t with
  | zero => simp at hdesc
  | succ k =>
      let b := fun i : ℕ => syracuseStep^[i] n
      let a := fun i : ℕ => (3 * b i + 1).factorization 2
      let K := n + (∑ i ∈ Finset.range (k + 1), a i) + 1
      have hbodd (i : ℕ) : Odd (b i) := syracuse_iterate_odd n hodd i
      have hstep (i : ℕ) : 3 * b i + 1 = 2 ^ (a i) * b (i + 1) := by
        change 3 * syracuseStep^[i] n + 1 =
          2 ^ ((3 * syracuseStep^[i] n + 1).factorization 2) * syracuseStep^[i + 1] n
        rw [Function.iterate_succ_apply']
        exact (Nat.ordProj_mul_ordCompl_eq_self (3 * syracuseStep^[i] n + 1) 2).symm
      have hapos (i : ℕ) : 0 < a i := by
        apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega)
        obtain ⟨u, hu⟩ := hbodd i
        exact ⟨3 * u + 2, by omega⟩
      have hcanonical : n < 2 ^ K := by
        exact lt_of_lt_of_le n.lt_two_pow_self
          (Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega))
      refine ⟨K, chainCertificate a b K k, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · simp [chainCertificate]
      · simp [chainCertificate]
      · rfl
      · exact chainCertificate_accepts a b K k hn hcanonical hodd
          (fun i _ => hapos i) (fun i _ => hstep i) (fun i _ => hbodd (i + 1))
          (by dsimp [K]; omega) hdesc

end CollatzFrontierAux

open CollatzFrontierAux

/-- Eventual descent is exactly acceptance by some adaptively sized dyadic certificate.
This equivalence supplies no uniform time, modulus, or termination bound.
Transcribed verbatim from `CollatzFrontier.eventual_descent_iff_certificate`
(main @ 4d656b9), reducing its forward direction to the imported
`chainCertificate_accepts` platform theorem. -/
theorem solution (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (∃ t : ℕ, syracuseStep^[t] n < n) ↔
      ∃ K : ℕ, ∃ cert : DescentCertificate,
        cert.start.constant = n ∧ cert.start.coefficient = 2 ^ K ∧
        checkDescent cert = true := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨K, cert, hr, hM, _, _, hc⟩ := finite_descent_has_certificate n t hn hodd ht
    exact ⟨K, cert, hr, hM, hc⟩
  · rintro ⟨K, cert, hr, _, hc⟩
    refine ⟨cert.exactRows.length + 1, ?_⟩
    simpa [AffineState.eval, hr] using checkDescent_sound cert hc 0
