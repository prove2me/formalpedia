-- Prove2me | solution 2 for Diaz.indep_of_algebraic_product
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:34:25.398791+00:00
-- url     : https://prove2.me/submissions/fdb6324f-0a58-4ab7-a62a-13bd5b1c1964

/-
`Diaz.indep_of_algebraic_product` through `Diaz.binary_form_eq_zero`.

Multiplying the relation by `p` gives `C p² + A p + B(pν) = 0` with all three
coefficients in `K`, so the node is "`1`, `p`, `p²` are `K`-independent" plus
the division by `pν ≠ 0`. That independence is `Diaz.binary_form_eq_zero` in its
degenerate case `y = 1`, `d = 2`.

The previous accepted proof carried a private `noquad_aux` — the same statement,
proved by hand from `transcendental_iff_injective` — and so did the accepted
proof of `Diaz.no_holo_stab`. Both now sit over the published node instead,
alongside `Diaz.forced_plane_exhaustion` and `Diaz.det_pencil_eq_conic`.

## Redundant hypotheses

None. `hβ` places the constant coefficient in `K`; `hβ0` is what turns
`B (pν) = 0` into `B = 0`.
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

theorem solution {K : Subfield ℂ} {p ν : ℂ}
    (hp : Transcendental K p) (hβ : p * ν ∈ K) (hβ0 : p * ν ≠ 0)
    {A B C : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
    (h : A + B * ν + C * p = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have key : C * p ^ 2 + A * p + B * (p * ν) = 0 := by linear_combination p * h
  obtain ⟨h1, h2, h3⟩ := gr_noquad hp hC hA (mul_mem hB hβ) key
  refine ⟨h2, ?_, h1⟩
  rcases mul_eq_zero.mp h3 with hb | hpv
  · exact hb
  · exact absurd hpv hβ0
