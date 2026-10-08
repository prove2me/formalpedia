-- Prove2me | solution 1 for CollatzFrontier.bounded_descent_generated
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:09:43.39054+00:00
-- url     : https://prove2.me/submissions/1e368f71-bf42-4a43-8856-7e5992f253e9

import Definitions.Def_collatzFrontierCertificate
import Theorems.Thm_CollatzFrontier_chainCertificate_accepts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open CollatzFrontier

namespace CollatzFrontierAux

/-! Helper lemmas, transcribed from `UniformDescent.lean`, `GeneratedCertificate.lean`,
`CertificateCompleteness.lean`, and `ExplicitCertificate.lean`
(research/executable-coverage-20261002 @ 3835de1). -/

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

/-- Bounded exponent search is exact once the supplied fuel covers the true exponent. -/
theorem candidateExponent_of_factor (e fuel c : ℕ) (hc : c % 2 = 1) (he : e ≤ fuel) :
    candidateExponent fuel (2 ^ e * c) = e := by
  induction e generalizing fuel with
  | zero =>
      cases fuel with
      | zero => rfl
      | succ fuel => simp [candidateExponent, hc]
  | succ e ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have he' : e ≤ fuel := by omega
          have hmul : 2 ^ (e + 1) * c = (2 ^ e * c) * 2 := by rw [pow_succ]; ring
          rw [hmul]
          simp [candidateExponent, ih fuel he']

/-- Once the exponent is covered, an exact valid row is precisely the generated row. -/
theorem candidateRow_of_factor {s : AffineState} {row : CertificateRow}
    (fuel : ℕ)
    (hc : 3 * s.constant + 1 = 2 ^ row.exponent * row.next.constant)
    (hD : 3 * s.coefficient = 2 ^ row.exponent * row.next.coefficient)
    (hodd : row.next.constant % 2 = 1) (he : row.exponent ≤ fuel) :
    candidateRow fuel s = row := by
  rcases row with ⟨e, next⟩
  rcases next with ⟨c, D⟩
  have hsearch : candidateExponent fuel (3 * s.constant + 1) = e := by
    rw [hc]
    exact candidateExponent_of_factor e fuel c hodd he
  simp only [candidateRow, hsearch]
  simp [hc, hD]

/-- Exact-prefix execution composes across concatenated row lists. -/
theorem runExactPrefix_append (xs ys : List CertificateRow) (s u : AffineState)
    (hx : runExactPrefix s xs = some u) :
    runExactPrefix s (xs ++ ys) = runExactPrefix u ys := by
  induction xs generalizing s with
  | nil =>
      simp only [runExactPrefix, Option.some.injEq] at hx
      subst u
      rfl
  | cons x xs ih =>
      simp only [runExactPrefix] at hx
      split at hx
      next hv => simpa [runExactPrefix, hv] using ih x.next hx
      next => contradiction

/-- An accepted exact prefix is reconstructed by the candidate generator with enough fuel. -/
theorem candidatePrefix_reconstructs (rows : List CertificateRow) (s last : AffineState)
    (fuel : ℕ) (hrun : runExactPrefix s rows = some last)
    (hfuel : ∀ row ∈ rows, row.exponent ≤ fuel) :
    candidatePrefix fuel rows.length s = (rows, last) := by
  induction rows generalizing s with
  | nil =>
      simp only [runExactPrefix, Option.some.injEq] at hrun
      subst last
      rfl
  | cons row rows ih =>
      simp only [runExactPrefix] at hrun
      split at hrun
      next hv =>
        have hrow := candidateRow_of_factor fuel hv.2.1 hv.2.2.1 hv.2.2.2.1
          (hfuel row (by simp))
        have ht := ih row.next hrun (fun r hr => hfuel r (by simp [hr]))
        simp only [List.length_cons, candidatePrefix, hrow, ht]
      next => contradiction

/-- Explicit-fuel reconstruction, without choosing fuel from the row list. -/
theorem exact_certificate_is_generated_with_fuel (cert : DescentCertificate) (fuel : ℕ)
    (hc : checkDescent cert = true) (hodd : cert.terminal.next.constant % 2 = 1)
    (hprefix : ∀ row ∈ cert.exactRows, row.exponent ≤ fuel)
    (hterminal : cert.terminal.exponent ≤ fuel) :
    candidateCertificate fuel cert.exactRows.length
      cert.start.constant cert.start.coefficient = cert := by
  cases hrun : runExactPrefix cert.start cert.exactRows with
  | none => simp [checkDescent, hrun] at hc
  | some last =>
      simp only [checkDescent, hrun, decide_eq_true_eq] at hc
      have hp := candidatePrefix_reconstructs cert.exactRows cert.start last fuel hrun hprefix
      have hr := candidateRow_of_factor fuel hc.2.1.2.1 hc.2.1.2.2 hodd hterminal
      have hstart : AffineState.mk cert.start.constant cert.start.coefficient = cert.start := rfl
      simp only [candidateCertificate, hstart, hp, hr]

/-- A finite descent compiles at every sufficient explicit modulus and fuel. -/
theorem finite_descent_generated_at_budget (n t K fuel : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hcanonical : n < 2 ^ K)
    (hbudget : (∑ i ∈ Finset.range t, (3 * syracuseStep^[i] n + 1).factorization 2) ≤ K)
    (hfuel : ∀ i < t, (3 * syracuseStep^[i] n + 1).factorization 2 ≤ fuel)
    (hdesc : syracuseStep^[t] n < n) :
    checkDescent (candidateCertificate fuel (t - 1) n (2 ^ K)) = true := by
  cases t with
  | zero => simp at hdesc
  | succ k =>
      let b := fun i : ℕ => syracuseStep^[i] n
      let a := fun i : ℕ => (3 * b i + 1).factorization 2
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
      let cert := chainCertificate a b K k
      have hc : checkDescent cert = true :=
        chainCertificate_accepts a b K k hn hcanonical hodd
          (fun i _ => hapos i) (fun i _ => hstep i) (fun i _ => hbodd (i + 1)) hbudget hdesc
      have heq := exact_certificate_is_generated_with_fuel cert fuel hc
        (Nat.odd_iff.mp (hbodd (k + 1)))
        (by
          intro row hr
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
          have hik : i < k := List.mem_range.mp hi
          exact hfuel i (by omega))
        (hfuel k (by omega))
      have heq' : candidateCertificate fuel k n (2 ^ K) = cert := by
        simpa [cert, chainCertificate, b] using heq
      simpa only [Nat.add_sub_cancel] using heq' ▸ hc

theorem syracuse_step_le_four_mul (n : ℕ) (hn : 0 < n) : syracuseStep n ≤ 4 * n := by
  have h : syracuseStep n ≤ 3 * n + 1 := Nat.ordCompl_le _ 2
  omega

theorem syracuse_iterate_positive (n i : ℕ) (hn : 0 < n) : 0 < syracuseStep^[i] n := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)

theorem syracuse_iterate_lt_power (n L : ℕ) (hn : 0 < n) (hsize : n < 2 ^ L) (i : ℕ) :
    syracuseStep^[i] n < 2 ^ (L + 2 * i) := by
  induction i with
  | zero => simpa using hsize
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hb := syracuse_step_le_four_mul (syracuseStep^[i] n) (syracuse_iterate_positive n i hn)
      have he : L + 2 * (i + 1) = L + 2 * i + 2 := by omega
      rw [he, pow_add]
      norm_num
      nlinarith

theorem syracuse_valuation_explicit_bound (n L t i : ℕ) (hn : 0 < n)
    (hsize : n < 2 ^ L) (hi : i < t) :
    (3 * syracuseStep^[i] n + 1).factorization 2 ≤ L + 2 * t := by
  apply Nat.factorization_le_of_le_pow
  have hp := syracuse_iterate_lt_power n L hn hsize i
  have hpos := syracuse_iterate_positive n i hn
  have he : L + 2 * i + 2 ≤ L + 2 * t := by omega
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [pow_add 2 (L + 2 * i) 2] at hpow
  norm_num at hpow
  nlinarith

/-- Multiplying the exact divisions bounds the cumulative, not merely individual, budget. -/
theorem syracuse_weighted_iterate_bound (n t : ℕ) (hn : 0 < n) :
    2 ^ (∑ i ∈ Finset.range t, (3 * syracuseStep^[i] n + 1).factorization 2) *
      syracuseStep^[t] n ≤ 4 ^ t * n := by
  induction t with
  | zero => simp
  | succ t ih =>
      let S := ∑ i ∈ Finset.range t, (3 * syracuseStep^[i] n + 1).factorization 2
      let a := (3 * syracuseStep^[t] n + 1).factorization 2
      have hrow : 2 ^ a * syracuseStep^[t + 1] n = 3 * syracuseStep^[t] n + 1 := by
        rw [Function.iterate_succ_apply']
        exact Nat.ordProj_mul_ordCompl_eq_self (3 * syracuseStep^[t] n + 1) 2
      have hp := syracuse_iterate_positive n t hn
      have hrowle : 2 ^ a * syracuseStep^[t + 1] n ≤ 4 * syracuseStep^[t] n := by omega
      rw [Finset.sum_range_succ, pow_add]
      change 2 ^ S * 2 ^ a * syracuseStep^[t + 1] n ≤ _
      calc
        _ = 2 ^ S * (2 ^ a * syracuseStep^[t + 1] n) := by ring
        _ ≤ 2 ^ S * (4 * syracuseStep^[t] n) := Nat.mul_le_mul_left _ hrowle
        _ = 4 * (2 ^ S * syracuseStep^[t] n) := by ring
        _ ≤ 4 * (4 ^ t * n) := Nat.mul_le_mul_left _ ih
        _ = _ := by rw [pow_succ]; ring

theorem syracuse_total_valuation_budget (n L t : ℕ) (hn : 0 < n) (hsize : n < 2 ^ L) :
    (∑ i ∈ Finset.range t, (3 * syracuseStep^[i] n + 1).factorization 2) < L + 2 * t := by
  let S := ∑ i ∈ Finset.range t, (3 * syracuseStep^[i] n + 1).factorization 2
  have hp := syracuse_iterate_positive n t hn
  have hb := syracuse_weighted_iterate_bound n t hn
  have hpow : (2 : ℕ) ^ S < 2 ^ (L + 2 * t) := by
    calc
      _ ≤ 2 ^ S * syracuseStep^[t] n := by nlinarith [show (0 : ℕ) < 2 ^ S by positivity]
      _ ≤ 4 ^ t * n := hb
      _ < 4 ^ t * 2 ^ L := Nat.mul_lt_mul_of_pos_left hsize (by positivity)
      _ = _ := by rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_add]; congr 1; omega
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow

end CollatzFrontierAux

open CollatzFrontierAux

/-- Linear explicit fuel and modulus suffice for every descending orbit in a dyadic box.
Transcribed verbatim from `CollatzFrontier.bounded_descent_generated`
(research/executable-coverage-20261002 @ 3835de1), reducing to the imported
`chainCertificate_accepts` platform theorem. -/
theorem solution (n L t : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hsize : n < 2 ^ L) (hdesc : syracuseStep^[t] n < n) :
    checkDescent (candidateCertificate (L + 2 * t) (t - 1) n
      (2 ^ (L + 2 * t))) = true := by
  apply finite_descent_generated_at_budget n t (L + 2 * t) (L + 2 * t) hn hodd
  · exact lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (syracuse_total_valuation_budget n L t hn hsize).le
  · exact fun i hi => syracuse_valuation_explicit_bound n L t i hn hsize hi
  · exact hdesc
