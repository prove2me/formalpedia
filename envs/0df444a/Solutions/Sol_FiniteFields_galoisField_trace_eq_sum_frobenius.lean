-- Prove2me | solution 1 for FiniteFields.galoisField_trace_eq_sum_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:55:09.986622+00:00
-- url     : https://prove2.me/submissions/0ebaaff9-b9dc-4e3c-a71b-808573b62c93

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Weil.Kloosterman =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, foundation rungs W0.1 + W3.1 + W1.1

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder, ~13:30 entry). These
are the three cheap foundation nodes the Stepanov core (W4) and the moment layer
(W2) consume; each is either a genuinely new definition (the Kloosterman sum) or a
thin re-export of mature mathlib machinery under clean names.

* **W0.1 — the Kloosterman sum** (`kloosterman`): for `a b : ZMod p`,
  `S(a, b; p) = ∑_{t ∈ (ZMod p)ˣ} ψ(a·t + b·t⁻¹)` with `ψ = ZMod.stdAddChar`.
  Basic facts:
  - `norm_kloosterman_le` : the trivial bound `‖S‖ ≤ #(ZMod p)ˣ`
    (triangle inequality + `‖ψ‖ = 1`); specialised at prime `p` to `‖S‖ ≤ p − 1`
    (`norm_kloosterman_le_sub_one`).
  - `kloosterman_comm` : the symmetry `S(a, b) = S(b, a)` (`t ↦ t⁻¹` reindex).
  - `kloosterman_conj` / `kloosterman_im` : real-valuedness, `conj S = S`
    (`t ↦ −t` pairs a value with its conjugate).
  - `kloosterman_reindex_units` : the unit-rescale twist `S(a·c, b·c⁻¹) = S(a, b)`
    (`t ↦ c·t` reindex, `c` a unit).

* **W3.1 — Hasse-derivative multiplicity** (`X_sub_C_pow_dvd_iff_hasseDeriv`):
  Lemma 8, `(X − C x)^ℓ ∣ h ↔ ∀ k < ℓ, (hasseDeriv k h).eval x = 0`. Assembled from
  `Polynomial.X_sub_C_pow_dvd_iff`, `Polynomial.X_pow_dvd_iff`, `Polynomial.taylor_coeff`.

* **W1.1 — GaloisField plumbing** (`galoisField_*`): thin re-exports fixing the
  cardinality `#𝔽_{p^n} = p^n`, the Frobenius fixed-field fact `x^{p^n} = x`, and the
  absolute trace as a Frobenius-orbit sum `Tr(x) = ∑_{i<n} x^{p^i}`.
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate

/-! ### W0.1 — the Kloosterman sum -/

variable {p : ℕ} [NeZero p]

/-- The **Kloosterman sum** `S(a, b; p) = ∑_{t ∈ (ZMod p)ˣ} ψ(a·t + b·t⁻¹)`, where
`ψ = ZMod.stdAddChar` is the standard primitive additive character `j ↦ exp(2πi j / p)`.
The sum runs over the *units* of `ZMod p`, so `t⁻¹` is the group inverse. -/
noncomputable def kloosterman (a b : ZMod p) : ℂ :=
  ∑ t : (ZMod p)ˣ, ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))

/-- **Trivial bound.** `‖S(a, b; p)‖ ≤ #(ZMod p)ˣ` from the triangle inequality and
`‖ψ x‖ = 1`. -/
theorem norm_kloosterman_le (a b : ZMod p) :
    ‖kloosterman a b‖ ≤ (Fintype.card (ZMod p)ˣ : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun t _ => AddChar.norm_apply _ _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Trivial bound, prime form.** For prime `p`, `‖S(a, b; p)‖ ≤ p − 1`. -/
theorem norm_kloosterman_le_sub_one [Fact p.Prime] (a b : ZMod p) :
    ‖kloosterman a b‖ ≤ (p : ℝ) - 1 := by
  have hp : (1 : ℕ) ≤ p := (Fact.out : p.Prime).one_lt.le
  refine (norm_kloosterman_le a b).trans (le_of_eq ?_)
  rw [ZMod.card_units p, Nat.cast_sub hp, Nat.cast_one]

/-- **Symmetry.** `S(a, b; p) = S(b, a; p)`, via the reindex `t ↦ t⁻¹`. -/
theorem kloosterman_comm (a b : ZMod p) : kloosterman a b = kloosterman b a := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (b * (t : ZMod p) + a * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.inv_apply, inv_inv]
  congr 1
  ring

/-- **Real-valuedness.** `conj S(a, b; p) = S(a, b; p)`: the reindex `t ↦ −t`
pairs each summand `ψ(a·t + b·t⁻¹)` with its complex conjugate `ψ(−(a·t + b·t⁻¹))`. -/
theorem kloosterman_conj (a b : ZMod p) :
    conj (kloosterman a b) = kloosterman a b := by
  have hR : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne p)
  unfold kloosterman
  rw [map_sum, ← Equiv.sum_comp (Equiv.neg (ZMod p)ˣ)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  simp only [Equiv.neg_apply]
  congr 1
  have hinv : ((-t : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) = -t⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [hinv]
  simp only [Units.val_neg]
  ring

/-- Real-valuedness, imaginary-part form: `S(a, b; p)` has zero imaginary part. -/
theorem kloosterman_im (a b : ZMod p) : (kloosterman a b).im = 0 :=
  Complex.conj_eq_iff_im.mp (kloosterman_conj a b)

/-- **Unit twist.** For a unit `c`, `S(a·c, b·c⁻¹; p) = S(a, b; p)`, via the
unit-rescale reindex `t ↦ c·t`. Combined with `kloosterman_comm` this yields the
`S(m·a, m·b)` forms. -/
theorem kloosterman_reindex_units (a b : ZMod p) (c : (ZMod p)ˣ) :
    kloosterman (a * (c : ZMod p)) (b * ((c⁻¹ : (ZMod p)ˣ) : ZMod p)) = kloosterman a b := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.mulLeft c)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul]
  congr 1
  ring

/-! ### W3.1 — Hasse-derivative multiplicity (Lemma 8) -/

open Polynomial in
/-- **W3.1 (Lemma 8).** A power `(X − C x)^ℓ` divides `h` iff all Hasse derivatives of
order `< ℓ` vanish at `x`. This is the multiplicity criterion the Stepanov auxiliary
polynomial uses to certify a high-order zero of the auxiliary function at each point of
the `D`-locus. The `←` direction (vanishing derivatives ⇒ high divisibility) is the
load-bearing one. Assembled from `X_sub_C_pow_dvd_iff` (translate to a zero at the origin),
`X_pow_dvd_iff` (divisibility ↔ low coefficients vanish), and `taylor_coeff` (the Taylor
coefficient at `x` is the Hasse derivative evaluated at `x`). -/
theorem X_sub_C_pow_dvd_iff_hasseDeriv {F : Type*} [CommRing F] (h : F[X]) (x : F) (ℓ : ℕ) :
    (X - C x) ^ ℓ ∣ h ↔ ∀ k < ℓ, (hasseDeriv k h).eval x = 0 := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, taylor_coeff]

/-! ### W1.1 — GaloisField plumbing -/

section GaloisFieldPlumbing

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The Galois field `𝔽_{p^n} = GaloisField p n` has exactly `p ^ n` elements. -/
theorem galoisField_card (h : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n h

/-- **Frobenius fixed field.** Every element of `𝔽_{p^n}` is fixed by the `n`-th iterate of
Frobenius: `x ^ (p ^ n) = x`. -/
theorem galoisField_pow_card (h : n ≠ 0) (x : GaloisField p n) : x ^ p ^ n = x := by
  letI := Fintype.ofFinite (GaloisField p n)
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n h]
  rw [← hcard]; exact FiniteField.pow_card x

/-- The absolute trace `𝔽_{p^n} → 𝔽_p` expanded as the Frobenius-orbit sum, in the raw
mathlib form (`Nat.card (ZMod p)` base, `finrank`-indexed range). -/
theorem galoisField_algebraMap_trace_eq_sum_pow (x : GaloisField p n) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = ∑ i ∈ Finset.range (Module.finrank (ZMod p) (GaloisField p n)),
          x ^ (Nat.card (ZMod p) ^ i) :=
  FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) (GaloisField p n) x

/-- **Absolute trace as Frobenius-orbit sum, clean form.** For `n ≠ 0`,
`algebraMap (Tr x) = ∑_{i < n} x ^ (p ^ i)` — the trace pushed into `𝔽_{p^n}` is the sum of
the Frobenius conjugates of `x`. -/
theorem galoisField_trace_eq_sum_frobenius (h : n ≠ 0) (x : GaloisField p n) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = ∑ i ∈ Finset.range n, x ^ (p ^ i) := by
  rw [galoisField_algebraMap_trace_eq_sum_pow, GaloisField.finrank p h, Nat.card_zmod]

end GaloisFieldPlumbing

end Salt.Weil

end




theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) (h : n ≠ 0) (x : GaloisField p n) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = ∑ i ∈ Finset.range n, x ^ (p ^ i) :=
  Salt.Weil.galoisField_trace_eq_sum_frobenius p n h x

