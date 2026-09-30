-- Prove2me | solution 1 for Complex.summable_taylorSeries_neg_log
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:21:51.23218+00:00
-- url     : https://prove2.me/submissions/300879f1-15c7-4bac-9de3-d75671c0d2a2

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_TauCeti_summable_mul_norm_pow_succ

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Taylor series of `-log (1 - ·)` summed over a family

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
-/

 section

namespace Complex
end Complex
section Complex
open Complex

/-- **The Taylor family of `-log (1 - rᵢ)` is summable over index and exponent together.**  For a
summable family `r` of complex numbers, all of modulus less than one, the double family
`(i, e) ↦ rᵢ ^ (e + 1) / (e + 1)` is absolutely summable, so its sum may be taken fibrewise.

Both hypotheses are needed, and neither is arithmetic: see the module docstring for why
`∀ i, ‖r i‖ < 1` alone does not suffice. -/
theorem solution {ι : Type*} {r : ι → ℂ} (hr : _root_.Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    _root_.Summable fun ie : ι × ℕ ↦ r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) := by
  -- The majorant is the weighted geometric bound at weight `1`; summability of `r` supplies its
  -- eventual bound with `ε = 1 / 2`.
  have hhalf : ∀ᶠ i in _root_.Filter.cofinite, ‖r i‖ ≤ 1 / 2 :=
    hr.tendsto_cofinite_zero.norm.eventually_le_const (by norm_num)
  have hbd : ∃ ε > 0, ∀ᶠ i in _root_.Filter.cofinite, (1 : ℝ) ≠ 0 → ‖r i‖ ≤ 1 - ε :=
    ⟨1 / 2, by norm_num, by filter_upwards [hhalf] with i hi _; linarith⟩
  have hmaj : _root_.Summable fun ie : ι × ℕ ↦ ‖r ie.1‖ ^ (ie.2 + 1) := by
    simpa using _root_.TauCeti.summable_mul_norm_pow_succ (w := fun _ ↦ (1 : ℝ)) hbd
      (by simpa using hr.norm) (fun i _ ↦ h1 i)
  refine hmaj.of_norm_bounded ?_
  rintro ⟨i, e⟩
  rw [_root_.norm_div, _root_.norm_pow]
  refine _root_.div_le_self (by positivity) ?_
  have hcast : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, _root_.Complex.norm_natCast]
  exact_mod_cast _root_.Nat.succ_le_succ (_root_.Nat.zero_le e)




end Complex

end
end
