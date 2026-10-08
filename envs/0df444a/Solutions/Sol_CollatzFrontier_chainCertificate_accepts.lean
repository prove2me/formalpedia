-- Prove2me | solution 1 for CollatzFrontier.chainCertificate_accepts
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:09:42.396039+00:00
-- url     : https://prove2.me/submissions/4389a470-daa8-4240-935a-94ab33814698

import Definitions.Def_collatzFrontierCertificate
import Mathlib.Tactic.Ring

open CollatzFrontier

namespace CollatzFrontierAux

/-! Helper lemmas, transcribed from the repo's `AffineStep`-free core of
`AffineDrift.lean`, `TerminalBudget.lean`, and `CertificateCompleteness.lean`
(research/executable-coverage-20261002 @ 3835de1, stacking on main @ 4d656b9). -/

/-- Every affine `3x+1` row produces strict cross-product drift. -/
theorem affine_row_strict_drift {r M b A c D d : ℕ}
    (hM : 0 < M) (hc : 3 * b + 1 = d * c) (hD : 3 * A = d * D)
    (hprior : r * A ≤ M * b) : r * D < M * c := by
  have hscaled : d * (r * D) < d * (M * c) := by
    calc
      d * (r * D) = r * (d * D) := by ring
      _ = 3 * (r * A) := by rw [← hD]; ring
      _ ≤ 3 * (M * b) := Nat.mul_le_mul_left 3 hprior
      _ < 3 * (M * b) + M := by omega
      _ = M * (3 * b + 1) := by ring
      _ = d * (M * c) := by rw [hc]; ring
  exact Nat.lt_of_mul_lt_mul_left hscaled

/-- Accepted exact prefixes preserve nonnegative affine intercept drift, including `[]`. -/
theorem runExactPrefix_drift (rows : List CertificateRow)
    (s result : AffineState) {r M : ℕ} (hM : 0 < M)
    (hprior : r * s.coefficient ≤ M * s.constant)
    (h : runExactPrefix s rows = some result) :
    r * result.coefficient ≤ M * result.constant := by
  induction rows generalizing s with
  | nil =>
      simp only [runExactPrefix, Option.some.injEq] at h
      subst result
      exact hprior
  | cons row rest ih =>
      simp only [runExactPrefix] at h
      split at h
      next hrow =>
        have hd := affine_row_strict_drift hM hrow.2.1 hrow.2.2.1 hprior
        exact ih row.next hd.le h
      next => contradiction

/-- The terminal row makes the drift strict even when the exact prefix is empty. -/
theorem terminal_certificate_strict_drift (rows : List CertificateRow)
    (s last : AffineState) (terminal : CertificateRow)
    (hM : 0 < s.coefficient)
    (h : runExactPrefix s rows = some last)
    (ht : TerminalRowValid last terminal) :
    s.constant * terminal.next.coefficient < s.coefficient * terminal.next.constant := by
  have hp := runExactPrefix_drift rows s last (r := s.constant) hM
    (by rw [Nat.mul_comm]) h
  exact affine_row_strict_drift hM ht.2.1 ht.2.2 hp

/-- Representative nonincrease alone forces a strictly smaller affine slope. -/
theorem terminal_coefficient_lt_of_representative_le (rows : List CertificateRow)
    (s last : AffineState) (terminal : CertificateRow)
    (hM : 0 < s.coefficient)
    (h : runExactPrefix s rows = some last)
    (ht : TerminalRowValid last terminal)
    (hB : terminal.next.constant ≤ s.constant) :
    terminal.next.coefficient < s.coefficient := by
  have hd := terminal_certificate_strict_drift rows s last terminal hM h ht
  have hx : s.constant * terminal.next.coefficient < s.constant * s.coefficient := by
    calc
      _ < s.coefficient * terminal.next.constant := hd
      _ ≤ s.coefficient * s.constant := Nat.mul_le_mul_left _ hB
      _ = _ := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_left hx

/-- The separate slope comparison in `checkDescent` is algebraically redundant. -/
theorem checkDescentSimple_eq_checkDescent (cert : DescentCertificate) :
    checkDescentSimple cert = checkDescent cert := by
  cases hrun : runExactPrefix cert.start cert.exactRows with
  | none => simp [checkDescentSimple, checkDescent, hrun]
  | some last =>
      simp only [checkDescentSimple, checkDescent, hrun]
      congr 1
      apply propext
      constructor
      · rintro ⟨hs, ht, hB⟩
        have hM : 0 < cert.start.coefficient := lt_trans hs.1 hs.2.1
        exact ⟨hs, ht, hB,
          (terminal_coefficient_lt_of_representative_le _ _ _ _ hM hrun ht hB.le).le⟩
      · rintro ⟨hs, ht, hB, _⟩
        exact ⟨hs, ht, hB⟩

/-- Affine coefficient propagation under a finite power-of-two budget. -/
theorem coefficient_factor {K S e i : ℕ} (h : S + e ≤ K) :
    3 * (3 ^ i * 2 ^ (K - S)) =
      2 ^ e * (3 ^ (i + 1) * 2 ^ (K - (S + e))) := by
  have hs : K - S = e + (K - (S + e)) := by omega
  rw [hs, pow_add, pow_succ]
  ring

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

/-- Compile a finite indexed chain of valid rows into the executable prefix format. -/
theorem runExactPrefix_of_indexed_chain (s : ℕ → AffineState) (row : ℕ → CertificateRow)
    (k : ℕ) (hnext : ∀ i < k, (row i).next = s (i + 1))
    (hvalid : ∀ i < k, ExactRowValid (s i) (row i)) :
    runExactPrefix (s 0) ((List.range k).map row) = some (s k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hp := ih (fun i hi => hnext i (by omega)) (fun i hi => hvalid i (by omega))
      rw [List.range_succ, List.map_append, runExactPrefix_append _ _ _ _ hp]
      simp [runExactPrefix, hvalid k (by omega), hnext k (by omega)]

end CollatzFrontierAux

open CollatzFrontierAux

/-- A sufficiently fine canonical dyadic budget compiles a descending finite chain.
The final positive exponent leaves an even coefficient at every earlier exact row.
Transcribed verbatim from `CollatzFrontier.chainCertificate_accepts`
(research/executable-coverage-20261002 @ 3835de1). -/
theorem solution (a b : ℕ → ℕ) (K k : ℕ)
    (hbpos : 0 < b 0) (hcanonical : b 0 < 2 ^ K) (hbodd : Odd (b 0))
    (hapos : ∀ i ≤ k, 0 < a i)
    (hstep : ∀ i ≤ k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hbudget : (∑ i ∈ Finset.range (k + 1), a i) ≤ K)
    (hdesc : b (k + 1) < b 0) :
    checkDescent (chainCertificate a b K k) = true := by
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, a j
  let A : ℕ → ℕ := fun i => 3 ^ i * 2 ^ (K - S i)
  let s := fun i => AffineState.mk (b i) (A i)
  let row := fun i => CertificateRow.mk (a i) (s (i + 1))
  have hsucc (i : ℕ) : S (i + 1) = S i + a i := Finset.sum_range_succ a i
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ≤ S j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  have hcoeff {i : ℕ} (hi : i ≤ k) : 3 * A i = 2 ^ (a i) * A (i + 1) := by
    dsimp [A]
    rw [hsucc]
    apply coefficient_factor
    have hh := hmono (show i + 1 ≤ k + 1 by omega)
    change S (k + 1) ≤ K at hbudget
    rw [hsucc] at hh
    omega
  have heven {i : ℕ} (hi : i < k) : A (i + 1) % 2 = 0 := by
    have hh := hmono (show i + 1 ≤ k by omega)
    have he := hapos k le_rfl
    change S (k + 1) ≤ K at hbudget
    rw [hsucc] at hbudget
    have hpos : 0 < K - S (i + 1) := by omega
    have hexp : K - S (i + 1) = (K - S (i + 1) - 1) + 1 := by omega
    dsimp [A]
    rw [hexp]
    simp [pow_succ, Nat.mul_mod]
  have hrows : ∀ i < k, ExactRowValid (s i) (row i) := by
    intro i hi
    refine ⟨hapos i hi.le, hstep i hi.le, hcoeff hi.le, ?_, heven hi⟩
    exact Nat.odd_iff.mp (hodd i hi)
  have hrun : runExactPrefix (s 0) ((List.range k).map row) = some (s k) :=
    runExactPrefix_of_indexed_chain s row k (by intros; rfl) hrows
  have hK : 0 < K := by
    have he := hapos k le_rfl
    change S (k + 1) ≤ K at hbudget
    rw [hsucc] at hbudget
    omega
  have hstart : StartValid (s 0) := by
    have hpow : (2 : ℕ) ^ K % 2 = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
      simp [pow_succ]
    simpa [StartValid, s, A, S] using
      And.intro hbpos (And.intro hcanonical (And.intro (Nat.odd_iff.mp hbodd) hpow))
  have ht : TerminalRowValid (s k) (row k) :=
    ⟨hapos k le_rfl, hstep k le_rfl, hcoeff le_rfl⟩
  rw [← checkDescentSimple_eq_checkDescent]
  change (match runExactPrefix (s 0) ((List.range k).map row) with
    | none => false
    | some last => decide (StartValid (s 0) ∧ TerminalRowValid last (row k) ∧
        (row k).next.constant < (s 0).constant)) = true
  rw [hrun, decide_eq_true_eq]
  exact ⟨hstart, ht, hdesc⟩
