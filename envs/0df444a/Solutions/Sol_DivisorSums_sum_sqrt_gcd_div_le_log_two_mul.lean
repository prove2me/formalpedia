-- Prove2me | solution 1 for DivisorSums.sum_sqrt_gcd_div_le_log_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T16:13:49.626593+00:00
-- url     : https://prove2.me/submissions/4994a538-87c8-4b78-ad87-950db2e46f58

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Weil.GcdDivisorSum =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# (7.7d) — the gcd-weighted divisor sums (HB 1983, §7)

Source math: `docs/sources/hb1983-notes.md:815-830`.  Demand trace:
`docs/exploration/n7-prep-dossier-0806.md:79` (deduplicated input list, item 4) and `:282`
(gap list row 4, supplier **nobody**, *GENUINELY OPEN — elementary, unpriced, N7's own*).

This module is a **supply depot** for N7 (Lemma 10 does not live here).  It delivers the
arithmetic that HB's (7.7)/(7.8) chain consumes, with **explicit constants** in place of the
source's `≪`.  ⚠️ *This list is the module's contents; if a row is added, it is added here too —
see the note at the end of this docstring.*

**The two sums:**
* `sum_sqrt_gcd_div_le` — HB (7.7), second line:
  `∑_{s=1}^{n} (n,s)^{1/2}/s ≤ d(n)·(1 + log n)`.
* `sum_sqrt_gcd_dyadic_le` — the (7.8) intermediate, HB's *"by a method similar to (7.7)"*:
  `∑_{M<m≤2M} (n,m)^{1/2} ≤ 2·M·d(n)`.

**The consumer's shape** (HB writes (7.7) as `≪ d(k₀)·log(2k₀)`, not `d(k₀)(1+log k₀)`):
* `sum_sqrt_gcd_div_le_log_two_mul` — the same sum `≤ (log 2)⁻¹·d(n)·log(2n)`.

**The (7.8) divisor bookkeeping** (gap row 4's second half):
* `card_divisors_le_of_dvd` — `m ∣ n → d(m) ≤ d(n)`; mathlib has the subset, not the card.
* `sum_sqrt_gcd_dyadic_le_of_dvd` — the dyadic sum at a *divisor* `k₀` of `k`, folded to `d(k)`.

**The shared idea**, which both sums rest on:
* `sqrt_gcd_le_sum_sqrt_common_divisors` — `(n,m)^{1/2} ≤ ∑_{d ∣ n, d ∣ m} d^{1/2}`.

**Two NECESSITY witnesses**, landed rather than narrated so a successor inherits the check and
not the claim:
* `hdvd_is_load_bearing` — dropping `k₀ ∣ k` makes the folded row FALSE at `k₀=60, k=1, M=3`.
* `log_two_inv_not_removable` — dropping `1/log 2` makes the consumer-shape row FALSE at `n=1`.

Both are stated at `Real.sqrt` rather than `rpow (1/2)` deliberately: the interface of a theorem
is its statement **plus** the tactic reach its consumers get, and `Real.sqrt` is what `gcongr`,
`positivity` and `nlinarith` actually fire on.

## The architecture — one idea, both rows

The whole module rests on `sqrt_gcd_le_sum_sqrt_common_divisors`:

    (n,m)^{1/2} ≤ ∑_{d ∣ n, d ∣ m} d^{1/2}

valid because `(n,m)` **is** one of the terms and every term is `≥ 0` (`Finset.single_le_sum`).
Over-counting here is what buys the simplicity: no exact-gcd partition, no coprimality
bookkeeping, no Möbius inversion.  Swap the two sums (`Finset.sum_comm`), and each row then
reduces to bounding **one** of the `d(n)` terms and multiplying by the card:

* row A's term is a harmonic block, `d^{-1/2}·H_{n/d} ≤ 1 + log n`, via mathlib's
  `harmonic_le_one_add_log`;
* row B's term is a multiples count, `d^{1/2}·⌊2M/d⌋ ≤ 2M`, via
  `Nat.Ioc_filter_dvd_card_eq_div`.

## ⚠️ What is measured, and what the constants are worth

Dense scan (row A over `n = 1…3000`, row B over `n = 1…600 × M = 0…200`):

| row | worst `LHS/RHS` observed | where |
|---|---|---|
| A at `d(n)(1 + log n)` | **1.000000** — an equality | `n = 1` |
| B at `2·M·d(n)` | 0.5 | `n = 1`, `M = 1` |

So **row A's constant `1` is tight**, attained at the trivial point and nowhere else: the ratio
falls to `0.016` by `n = 720720`.  The row is loose exactly where it is consumed.

⛔ **Row B at the constant `1` is very probably TRUE and is deliberately NOT stated.**  The
over-count costs `d(n)·√(2M)` on top of `M·d(n)`, so `1` is unreachable **on this route** — a
route-break, not a false statement.  Conflating those two is the failure this corpus keeps
paying for (compare the `5(1 + log K)` entry in `flags.md` for the `L¹` row).  N7 consumes both
rows through a `≪`, so the constant is free and buying it back is worth nothing.

## ⚠️ A NOTE ON THIS DOCSTRING ITSELF

It said *"it delivers **the two** arithmetic sums"* while the module held **eight** theorems —
a claim that outran its object as rows were added under it (2026-08-08 night, caught by a
deliberate docstring-vs-contents sweep, not by the kernel).  **The kernel cannot check a
docstring**, so this list is maintained by hand: **add a row, add its line here.**
-/

namespace Salt.Weil

open scoped BigOperators
open Finset

/-! ### The over-count — the one shared idea -/

/-- **`(n,m)^{1/2} ≤ ∑_{d ∣ n, d ∣ m} d^{1/2}`.**  The gcd itself is one of the terms and the
rest are nonnegative, so this is `Finset.single_le_sum` and nothing else.  Over-counting is what
lets both rows below avoid an exact-gcd partition. -/
theorem sqrt_gcd_le_sum_sqrt_common_divisors (n m : ℕ) (hn : n ≠ 0) :
    Real.sqrt (Nat.gcd n m) ≤ ∑ d ∈ n.divisors.filter (· ∣ m), Real.sqrt d := by
  refine Finset.single_le_sum (f := fun d : ℕ => Real.sqrt (d : ℝ))
    (fun i _ => Real.sqrt_nonneg _) ?_
  simp only [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨Nat.gcd_dvd_left n m, hn⟩, Nat.gcd_dvd_right n m⟩

/-- `√d ≤ d` for `1 ≤ d`.  (mathlib has no `Real.sqrt_le_self`; this is the two-line
`sqrt_le_sqrt` + `sqrt_sq` route, used by both per-term cores.) -/
private lemma sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h1 : x ≤ x ^ 2 := by nlinarith
  calc Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt h1
    _ = x := Real.sqrt_sq (by linarith)

/-! ### Row A — HB (7.7), second line -/

/-- The multiples of `d` in `[1,n]` are exactly `d·[1, n/d]`, when `d ∣ n` and `d ≠ 0`. -/
private lemma filter_dvd_Icc_eq_image (n d : ℕ) (hd0 : d ≠ 0) (hdn : d ∣ n) :
    (Finset.Icc 1 n).filter (fun s => d ∣ s)
      = (Finset.Icc 1 (n / d)).image (fun t => d * t) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hs1, hsn⟩, t, rfl⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | h
      · simp at hs1
      · exact h
    · exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0)).mpr (by rwa [Nat.mul_comm])
  · rintro ⟨t, ⟨ht1, htn⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, t, rfl⟩
    · calc 1 = 1 * 1 := by ring
        _ ≤ d * t := Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr hd0) ht1
    · calc d * t ≤ d * (n / d) := Nat.mul_le_mul_left d htn
        _ = n := Nat.mul_div_cancel' hdn

/-- **Row A, per-term core.**  For `d ∣ n`, the harmonic block over the multiples of `d`
is at most `1 + log n`: reindex `s = d·t`, use `√d ≤ d` to drop to `∑ 1/t`, and apply
mathlib's `harmonic_le_one_add_log`. -/
private lemma rowA_term (n d : ℕ) (hn : n ≠ 0) (hd : d ∈ n.divisors) :
    ∑ s ∈ (Finset.Icc 1 n).filter (fun s => d ∣ s), Real.sqrt (d : ℝ) / s
      ≤ 1 + Real.log n := by
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdn)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hinj : Set.InjOn (fun t => d * t) ↑(Finset.Icc 1 (n / d)) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) hab
  rw [filter_dvd_Icc_eq_image n d hd0 hdn, Finset.sum_image hinj]
  have hterm : ∀ t ∈ Finset.Icc 1 (n / d),
      Real.sqrt (d : ℝ) / ((d * t : ℕ) : ℝ) ≤ ((t : ℝ))⁻¹ := by
    intro t ht
    have ht1 : (1 : ℕ) ≤ t := (Finset.mem_Icc.mp ht).1
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
    have hdpos : (0 : ℝ) < d := by linarith
    have hsq : Real.sqrt (d : ℝ) ≤ (d : ℝ) := sqrt_le_self_of_one_le hd1
    rw [Nat.cast_mul]
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ htpos]
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  calc ∑ t ∈ Finset.Icc 1 (n / d), Real.sqrt (d : ℝ) / ((d * t : ℕ) : ℝ)
      ≤ ∑ t ∈ Finset.Icc 1 (n / d), ((t : ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ = (harmonic (n / d) : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; ring_nf
    _ ≤ 1 + Real.log (n / d : ℕ) := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log n := by
        have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.div_le_self n d
        have hpos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by
          have h : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn)
            (Nat.pos_of_ne_zero hd0)
          exact_mod_cast h
        have := Real.log_le_log hpos hle
        linarith

/-- **(7.7), second line — the gcd-weighted harmonic sum.**  For `n ≠ 0`,

    ∑_{s = 1}^{n} (n,s)^{1/2} / s  ≤  d(n) · (1 + log n).

HB states this as `∑_{1≤s≤k₀} (k₀,s)^{1/2} s^{−1} ≪ d(k₀) log(2k₀)`
(`hb1983-notes.md:822`); the constant here is `1`, and it is **tight at `n = 1`**, where both
sides are exactly `1`. -/
theorem sum_sqrt_gcd_div_le (n : ℕ) (hn : n ≠ 0) :
    ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ (n.divisors.card : ℝ) * (1 + Real.log n) := by
  have hstep : ∀ s ∈ Finset.Icc 1 n,
      Real.sqrt (Nat.gcd n s : ℝ) / s
        ≤ ∑ d ∈ n.divisors, (if d ∣ s then Real.sqrt (d : ℝ) / s else 0) := by
    intro s hs
    have hs1 : (1 : ℕ) ≤ s := (Finset.mem_Icc.mp hs).1
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
    have h := sqrt_gcd_le_sum_sqrt_common_divisors n s hn
    calc Real.sqrt (Nat.gcd n s : ℝ) / s
        ≤ (∑ d ∈ n.divisors.filter (· ∣ s), Real.sqrt (d : ℝ)) / s := by gcongr
      _ = ∑ d ∈ n.divisors, (if d ∣ s then Real.sqrt (d : ℝ) / s else 0) := by
          rw [Finset.sum_div, Finset.sum_filter]
  calc ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ ∑ s ∈ Finset.Icc 1 n, ∑ d ∈ n.divisors,
          (if d ∣ s then Real.sqrt (d : ℝ) / s else 0) := Finset.sum_le_sum hstep
    _ = ∑ d ∈ n.divisors, ∑ s ∈ Finset.Icc 1 n,
          (if d ∣ s then Real.sqrt (d : ℝ) / s else 0) := Finset.sum_comm
    _ = ∑ d ∈ n.divisors, ∑ s ∈ (Finset.Icc 1 n).filter (fun s => d ∣ s),
          Real.sqrt (d : ℝ) / s := by
          exact Finset.sum_congr rfl fun d _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _d ∈ n.divisors, (1 + Real.log n) :=
          Finset.sum_le_sum fun d hd => rowA_term n d hn hd
    _ = (n.divisors.card : ℝ) * (1 + Real.log n) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **(7.7) IN THE CONSUMER'S LITERAL SHAPE.**  HB states the row as `≪ d(k₀)·log(2k₀)`
(`hb1983-notes.md:822`), **not** as `d(k₀)·(1 + log k₀)`.  The two differ by the constant
`1/log 2`, and this is the bridge.

⚠️ **Why this exists as its own row rather than as a remark.**  A supply row stated in a shape
the consumer does not use is a mismatch someone discovers *mid-wave*.  The `L¹` row already paid
this bill once on salt — `6(1+log K)` and `13 log K` are **incomparable at `K = 2`**, and the
obvious chaining does not typecheck.  Here the chaining *does* work, with constant `1/log 2`;
it is tight at `n = 1`, where both sides are exactly `1/log 2`. -/
theorem sum_sqrt_gcd_div_le_log_two_mul (n : ℕ) (hn : n ≠ 0) :
    ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ (Real.log 2)⁻¹ * (n.divisors.card : ℝ) * Real.log (2 * n) := by
  have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlogn : (0:ℝ) ≤ Real.log n := Real.log_nonneg h1
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (0:ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  have hbridge : 1 + Real.log n ≤ (Real.log 2)⁻¹ * Real.log (2 * n) := by
    rw [show ((2 : ℝ) * n) = 2 * (n : ℝ) from rfl,
      Real.log_mul (by norm_num) (by exact_mod_cast hn), inv_mul_eq_div, le_div_iff₀ hl2]
    nlinarith [hlogn, Real.log_two_lt_d9]
  calc ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ (n.divisors.card : ℝ) * (1 + Real.log n) := sum_sqrt_gcd_div_le n hn
    _ ≤ (n.divisors.card : ℝ) * ((Real.log 2)⁻¹ * Real.log (2 * n)) := by
        exact mul_le_mul_of_nonneg_left hbridge hcard
    _ = (Real.log 2)⁻¹ * (n.divisors.card : ℝ) * Real.log (2 * n) := by ring

/-- **The `1/log 2` in the row above is NECESSARY — witness, at `n = 1`.**  Dropping it gives
`∑ ≤ d(n)·log(2n)`, which is FALSE there: the sum is exactly `1` and `d(1)·log 2 = 0.693…`.

📌 Landed for the same reason as `hdvd_is_load_bearing`: a constant justified only in prose is a
claim, and a successor inherits the claim rather than the check. -/
theorem log_two_inv_not_removable :
    ¬ (∑ s ∈ Finset.Icc 1 1, Real.sqrt (Nat.gcd 1 s : ℝ) / s
        ≤ ((1 : ℕ).divisors.card : ℝ) * Real.log 2) := by
  have hsum : ∑ s ∈ Finset.Icc 1 1, Real.sqrt (Nat.gcd 1 s : ℝ) / s = 1 := by
    norm_num
  have hd : (((1 : ℕ).divisors.card : ℝ)) = 1 := by norm_num
  rw [hsum, hd]
  push Not
  nlinarith [Real.log_two_lt_d9]

/-! ### Row B — the (7.8) intermediate -/

/-- **Row B, per-term core.**  Uniformly in `d ∣ n`, the multiples of `d` in `(M, 2M]`
contribute at most `2M`: their count is at most `⌊2M/d⌋`, and `d^{1/2}·(2M/d) = 2M/√d ≤ 2M`.
No case split on `d ≤ 2M` is needed — the crude count already carries it. -/
private lemma rowB_term (n d M : ℕ) (hd : d ∈ n.divisors) :
    ∑ _m ∈ (Finset.Ioc M (2 * M)).filter (fun m => d ∣ m), Real.sqrt (d : ℝ)
      ≤ 2 * M := by
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hsub : (Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)
      ⊆ (Finset.Ioc 0 (2 * M)).filter (fun m => d ∣ m) := by
    apply Finset.filter_subset_filter
    intro x hx
    simp only [Finset.mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt (Nat.zero_le M) hx.1, hx.2⟩
  have hcard : ((Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)).card ≤ 2 * M / d := by
    calc ((Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)).card
        ≤ ((Finset.Ioc 0 (2 * M)).filter (fun m => d ∣ m)).card := Finset.card_le_card hsub
      _ = 2 * M / d := Nat.Ioc_filter_dvd_card_eq_div _ _
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : (((Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)).card : ℝ)
      ≤ ((2 * M : ℕ) : ℝ) / (d : ℝ) := by
    calc (((Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)).card : ℝ)
        ≤ ((2 * M / d : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ((2 * M : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hsqrt : Real.sqrt (d : ℝ) ≤ (d : ℝ) := sqrt_le_self_of_one_le hd1
  calc (((Finset.Ioc M (2 * M)).filter (fun m => d ∣ m)).card : ℝ) * Real.sqrt (d : ℝ)
      ≤ (((2 * M : ℕ) : ℝ) / (d : ℝ)) * Real.sqrt (d : ℝ) := by gcongr
    _ ≤ (((2 * M : ℕ) : ℝ) / (d : ℝ)) * (d : ℝ) := by gcongr
    _ = ((2 * M : ℕ) : ℝ) := by field_simp
    _ = 2 * M := by push_cast; ring

/-- **The (7.8) intermediate — the dyadic gcd sum.**  For `n ≠ 0` and every `M`,

    ∑_{M < m ≤ 2M} (n,m)^{1/2}  ≤  2 · M · d(n).

HB states it as `Σ_{M<m≤2M} (k₀,m)^{1/2} ≪ M·d(k₀)`, *"by a method similar to (7.7)"*
(`hb1983-notes.md:826`).  Holds at `M = 0` as `0 ≤ 0`.  ⚠️ The constant `2` is what **this
route** gives; `1` is measured true and is a route-break, see the module docstring. -/
theorem sum_sqrt_gcd_dyadic_le (n M : ℕ) (hn : n ≠ 0) :
    ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt (Nat.gcd n m : ℝ)
      ≤ 2 * M * (n.divisors.card : ℝ) := by
  calc ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt (Nat.gcd n m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc M (2 * M), ∑ d ∈ n.divisors,
          (if d ∣ m then Real.sqrt (d : ℝ) else 0) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h := sqrt_gcd_le_sum_sqrt_common_divisors n m hn
        rwa [Finset.sum_filter] at h
    _ = ∑ d ∈ n.divisors, ∑ m ∈ Finset.Ioc M (2 * M),
          (if d ∣ m then Real.sqrt (d : ℝ) else 0) := Finset.sum_comm
    _ = ∑ d ∈ n.divisors, ∑ _m ∈ (Finset.Ioc M (2 * M)).filter (fun m => d ∣ m),
          Real.sqrt (d : ℝ) := by
        exact Finset.sum_congr rfl fun d _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _d ∈ n.divisors, (2 * M : ℝ) :=
        Finset.sum_le_sum fun d hd => rowB_term n d M hd
    _ = 2 * M * (n.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The `hdvd : k₀ ∣ k` hypothesis of `sum_sqrt_gcd_dyadic_le_of_dvd` is LOAD-BEARING — and
this is its WITNESS, as a kernel fact rather than a claim in a commit message.**

At `k₀ = 60`, `k = 1`, `M = 3` the folded conclusion is FALSE:
`√4 + √5 + √6 = 6.6856… > 6 = 2·M·d(1)`.

📌 **Landed deliberately, and the reason generalises.**  A mutation control that lives only in
`flags.md` is a *claim that it once fired*: a successor inherits my word, not the firing.  The
statement below is re-checked by every build, by every hand, forever — so the necessity of that
hypothesis survives me.  (Its sibling controls in this module cannot be landed the same way: a
mutation makes the *build* fail, and a failing build cannot live in the repo.  The WITNESS can,
and the witness is the mathematical content.) -/
theorem hdvd_is_load_bearing :
    ¬ (∑ m ∈ Finset.Ioc 3 6, Real.sqrt (Nat.gcd 60 m : ℝ)
        ≤ 2 * 3 * ((1 : ℕ).divisors.card : ℝ)) := by
  -- the three gcds, evaluated ONCE each (unfolding `Nat.gcd` as a simp lemma blows maxRecDepth)
  have g4 : Nat.gcd 60 4 = 4 := by decide
  have g5 : Nat.gcd 60 5 = 5 := by decide
  have g6 : Nat.gcd 60 6 = 6 := by decide
  have hset : Finset.Ioc 3 6 = ({4, 5, 6} : Finset ℕ) := by decide
  have hsum : ∑ m ∈ Finset.Ioc 3 6, Real.sqrt (Nat.gcd 60 m : ℝ)
      = Real.sqrt 4 + Real.sqrt 5 + Real.sqrt 6 := by
    rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, g4, g5, g6]
    norm_num
    ring
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- `√5 > 2` and `√6 > 2`, each on its own: if `√5 ≤ 2` then `5 = √5² ≤ 4`.
  have b5 : (2:ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg (5:ℝ)]
  have b6 : (2:ℝ) < Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), Real.sqrt_nonneg (6:ℝ)]
  have hd : ((1 : ℕ).divisors.card : ℝ) = 1 := by norm_num
  rw [hsum, h4, hd]
  push Not
  linarith [b5, b6]

/-! ### The divisor bookkeeping for (7.8) — the `d(k₀) ≤ d(k)` fold

The second half of dossier gap-list row 4 (*"+ divisor bookkeeping for (7.8)"*).  It is the step
the source's corrected derivation spends when it says *"folding `d(k₀) ≤ d(k)` (valid as
`k₀ ∣ k`) turns `d(k)²·d(k₀)` into `d(k)³`"* (`hb1983-notes.md`, the 2026-08-06 correction block
under (7.8)).  mathlib has `Nat.divisors_subset_of_dvd` but **not** the card consequence. -/

/-- **`d` is monotone under divisibility**: `m ∣ n` and `n ≠ 0` give `d(m) ≤ d(n)`.
`Nat.divisors_subset_of_dvd` plus `Finset.card_le_card`; mathlib carries the former and not
this. -/
theorem card_divisors_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    m.divisors.card ≤ n.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hn hmn)

/-- **The (7.8) fold, in the shape the derivation consumes.**  The dyadic gcd sum taken at a
*divisor* `k₀` of `k`, bounded by `d(k)` rather than `d(k₀)` — this is what converts
`d(k)²·d(k₀)` into `d(k)³` in HB's passage from the intermediate `S_m` step to (7.8).
⚠️ `hdvd` is load-bearing: at `k₀ = 60`, `k = 1`, `M = 3` the conclusion is FALSE
(`√4 + √5 + √6 = 6.685 > 6 = 2·3·d(1)`). -/
theorem sum_sqrt_gcd_dyadic_le_of_dvd {k₀ k M : ℕ} (hk : k ≠ 0) (hdvd : k₀ ∣ k) :
    ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt (Nat.gcd k₀ m : ℝ)
      ≤ 2 * M * (k.divisors.card : ℝ) := by
  -- see `hdvd_is_load_bearing` below: without `hdvd` this statement is FALSE.
  have hk₀ : k₀ ≠ 0 := by
    rintro rfl; exact hk (Nat.eq_zero_of_zero_dvd hdvd)
  have hcard : (k₀.divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast card_divisors_le_of_dvd hk hdvd
  calc ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt (Nat.gcd k₀ m : ℝ)
      ≤ 2 * M * (k₀.divisors.card : ℝ) := sum_sqrt_gcd_dyadic_le k₀ M hk₀
    _ ≤ 2 * M * (k.divisors.card : ℝ) := by
        have hM : (0 : ℝ) ≤ 2 * M := by positivity
        exact mul_le_mul_of_nonneg_left hcard hM

end Salt.Weil

end




theorem solution (n : ℕ) (hn : n ≠ 0) :
    ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ (Real.log 2)⁻¹ * (n.divisors.card : ℝ) * Real.log (2 * n) :=
  Salt.Weil.sum_sqrt_gcd_div_le_log_two_mul n hn

