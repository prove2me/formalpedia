-- Prove2me | solution 1 for BitDFT.packed_scale_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T21:57:20.713974+00:00
-- url     : https://prove2.me/submissions/7c3d5cee-12c0-4499-a3aa-4d9f2578fd90

import Definitions.Def_BitDFT_PackedScale
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT.PackedScale IntMul

/-- Multiplying the packed integer by n multiplies each coefficient by n. -/
theorem packed_scale_identity_proof (B n : ℕ) (xs : List ℕ) :
    packBase B (xs.map (fun a => n * a)) = n * packBase B xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, packBase]
    rw [ih]
    ring

/-- If every coefficient is below the base, the packed integer fits in one
    base digit per coefficient. -/
theorem packed_bound_proof (B : ℕ) (hB : 0 < B) (xs : List ℕ)
    (hxs : ∀ a ∈ xs, a < B) :
    packBase B xs < B ^ xs.length := by
  induction xs with
  | nil => simp [packBase]
  | cons a xs ih =>
    have ha : a < B := hxs a (by simp)
    have htail : ∀ x ∈ xs, x < B := by
      intro x hx
      exact hxs x (by simp [hx])
    have ht := ih htail
    simp only [packBase, List.length_cons, Nat.pow_succ]
    nlinarith

/-- Scaling q-bit coefficients by n creates no overlap when each packed digit
    has q+ell(n)+1 bits. This is the arithmetic core of the block scaler. -/
theorem scaled_coefficients_fit_proof (n q ell : ℕ) (hn : n ≤ 2 ^ ell)
    (xs : List ℕ) (hxs : ∀ a ∈ xs, a < 2 ^ q) :
    (∀ a ∈ xs.map (fun a => n * a), a < 2 ^ (q + ell + 1)) ∧
    packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) =
      n * packBase (2 ^ (q + ell + 1)) xs ∧
    packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) <
      (2 ^ (q + ell + 1)) ^ xs.length := by
  have hcoeff : ∀ a ∈ xs, n * a < 2 ^ (q + ell + 1) := by
    intro a ha
    calc
      n * a ≤ 2 ^ ell * a := Nat.mul_le_mul_right a hn
      _ < 2 ^ ell * 2 ^ q := Nat.mul_lt_mul_of_pos_left (hxs a ha) (by positivity)
      _ = 2 ^ q * 2 ^ ell := Nat.mul_comm _ _
      _ = 2 ^ (q + ell) := (pow_add 2 q ell).symm
      _ < 2 ^ (q + ell + 1) := by
        rw [Nat.pow_succ]
        have hp : 0 < 2 ^ (q + ell) := Nat.pow_pos (by decide)
        omega
  have hbase : 0 < 2 ^ (q + ell + 1) := Nat.pow_pos (by decide)
  have hscaled : ∀ a ∈ xs.map (fun a => n * a), a < 2 ^ (q + ell + 1) := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨a₀, ha₀, rfl⟩
    exact hcoeff a₀ ha₀
  have hpack := packed_bound_proof (2 ^ (q + ell + 1)) hbase
    (xs.map (fun a => n * a)) hscaled
  rw [List.length_map] at hpack
  exact ⟨hscaled, packed_scale_identity_proof _ _ _, hpack⟩

/-- At least a fourth of n slots fit in an nq-bit multiplier operand when
    q≥ell(n); therefore at most five packed calls cover n coefficients. -/
theorem chunk_width_proof (n q ell r : ℕ) (hq : 1 ≤ q) (hell : ell ≤ q)
    (hslots : 4 * r ≤ n) : r * (q + ell + 1) ≤ n * q := by
  have hw : q + ell + 1 ≤ 3 * q := by omega
  calc
    r * (q + ell + 1) ≤ r * (3 * q) := Nat.mul_le_mul_left r hw
    _ ≤ (4 * r) * q := by nlinarith
    _ ≤ n * q := Nat.mul_le_mul_right q hslots

/-- Five chunks of floor(n/4) coefficients suffice once n≥12. -/
theorem five_chunks_proof (n : ℕ) (hn : 12 ≤ n) :
    n ≤ 5 * (n / 4) := by
  have hmod := Nat.mod_lt n (by decide : 0 < 4)
  have hdecomp := Nat.mod_add_div n 4
  omega

/-- A bounded number of packed calls suffices for exact vector scaling. -/
theorem solution :
    (∀ B n xs, packBase B (xs.map (fun a => n * a)) = n * packBase B xs) ∧
    (∀ B, 0 < B → ∀ xs, (∀ a ∈ xs, a < B) → packBase B xs < B ^ xs.length) ∧
    (∀ n q ell, n ≤ 2 ^ ell → ∀ xs, (∀ a ∈ xs, a < 2 ^ q) →
      (∀ a ∈ xs.map (fun a => n * a), a < 2 ^ (q + ell + 1)) ∧
      packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) =
        n * packBase (2 ^ (q + ell + 1)) xs ∧
      packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) <
        (2 ^ (q + ell + 1)) ^ xs.length) ∧
    (∀ n q ell r, 1 ≤ q → ell ≤ q → 4 * r ≤ n →
      r * (q + ell + 1) ≤ n * q) ∧
    (∀ n, 12 ≤ n → n ≤ 5 * (n / 4)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B n xs
    exact packed_scale_identity_proof B n xs
  · intro B hB xs hxs
    exact packed_bound_proof B hB xs hxs
  · intro n q ell hn xs hxs
    exact scaled_coefficients_fit_proof n q ell hn xs hxs
  · intro n q ell r hq hell hslots
    exact chunk_width_proof n q ell r hq hell hslots
  · intro n hn
    exact five_chunks_proof n hn
