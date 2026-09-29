-- Prove2me | solution 2 for Diaz.no_holo_stab
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:34:24.828029+00:00
-- url     : https://prove2.me/submissions/77997a1d-6136-41ef-847f-2cf8c5c719ea

/-
`Diaz.no_holo_stab` through `Diaz.binary_form_eq_zero`.

Clearing the denominator turns the fixed-point equation into
`c z² + (d - a) z + (-b) = 0` with all three coefficients in `K`, so the node is
"`1`, `z`, `z²` are `K`-independent" plus bookkeeping. That independence is
`Diaz.binary_form_eq_zero` in its degenerate case `y = 1`, `d = 2`.

The previous accepted proof carried a private `noquad_aux` — the same statement,
proved by hand from `transcendental_iff_injective` — and so did the accepted
proof of `Diaz.indep_of_algebraic_product`. Both now sit over the published
node instead, alongside `Diaz.forced_plane_exhaustion` and
`Diaz.det_pencil_eq_conic`.

## Redundant hypotheses

None. `hden` is needed to clear the denominator; `ha, hb, hc, hd` place the
three coefficients in `K`.
-/
import Mathlib
import Theorems.Thm_Diaz_binary_form_eq_zero

open ComplexConjugate

/-- `1`, `p`, `p²` are `K`-independent for `p` transcendental over `K`.
This is `Diaz.binary_form_eq_zero` in its degenerate case `y = 1`, `d = 2`:
a binary form in `(p, 1)` is a polynomial in `p`, and `Transcendental K (p/1)`
is `Transcendental K p`. -/
private theorem gr_noquad {K : Subfield ℂ} {p : ℂ} (hp : Transcendental K p)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (h : a * p ^ 2 + b * p + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  set k : ℕ → ℂ := fun i => if i = 0 then c else if i = 1 then b else if i = 2 then a else 0
    with hk
  have hkK : ∀ i, k i ∈ K := by
    intro i
    simp only [hk]
    split_ifs
    exacts [hc, hb, ha, K.zero_mem]
  have hsum : ∑ i ∈ Finset.range (2 + 1), k i * p ^ i * (1 : ℂ) ^ (2 - i) = 0 := by
    simp only [hk, Finset.sum_range_succ, Finset.sum_range_zero, one_pow, mul_one]
    norm_num
    linear_combination h
  have hz := Diaz.binary_form_eq_zero (y := (1 : ℂ)) one_ne_zero (by simpa using hp) 2 k hkK hsum
  refine ⟨?_, ?_, ?_⟩
  · simpa [hk] using hz 2 (by norm_num)
  · simpa [hk] using hz 1 (by norm_num)
  · simpa [hk] using hz 0 (by norm_num)

theorem solution {K : Subfield ℂ} {z : ℂ} (hz : Transcendental K z)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hden : c * z + d ≠ 0) (h : (a * z + b) / (c * z + d) = z) :
    c = 0 ∧ b = 0 ∧ a = d := by
  have h' : a * z + b = z * (c * z + d) := by
    rw [div_eq_iff hden] at h
    linear_combination h
  have key : c * z ^ 2 + (d - a) * z + (-b) = 0 := by linear_combination -h'
  obtain ⟨h1, h2, h3⟩ := gr_noquad hz hc (sub_mem hd ha) (neg_mem hb) key
  exact ⟨h1, neg_eq_zero.mp h3, (sub_eq_zero.mp h2).symm⟩
