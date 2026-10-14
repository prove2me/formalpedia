-- Prove2me | solution 1 for DiazModulus.two_orbit_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:34:25.062988+00:00
-- url     : https://prove2.me/submissions/9fda2d9b-3ab1-4cdf-a630-d411bedbe4f6

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The two-orbit space excludes squares and reciprocals

Let `u ∉ Q̄`, `a, b, α, β, γ, δ ∈ Q̄` non-zero with `a² ≠ b²`, `g₁ = α/(u − a) + β/(u + a)`,
`g₂ = γ/(u − b) + δ/(u + b)` and `W = span_Q̄ {1, u, u⁻¹, g₁, g₂}`.

Everything rests on one residue lemma (`residue`): if
`c₀ + c₁u + c₂u² + d (u − p)⁻¹ + Σᵢ eᵢ (u − qᵢ)⁻¹ = 0` (five `qᵢ`, all `≠ p`, everything in
`Q̄`), then `d = 0`. Multiplying by `(u − p) Πᵢ (u − qᵢ)` gives a `Q̄`-polynomial vanishing at the
transcendental `u`, hence the zero polynomial; its value at `p` is `d Πᵢ (p − qᵢ)`. With the poles
`0, a, −a, b, −b` (distinct, since `a, b ≠ 0`, `a² ≠ b²`) every residue of a relation vanishes
(`residues`).
* Freeness: the residues of `c₀ + c₁u + c₂u⁻¹ + c₃g₁ + c₄g₂` are `c₂, c₃α, c₃β, c₄γ, c₄δ`; then
  `c₀ + c₁u = 0` forces `c₀ = c₁ = 0`, as `u ∉ Q̄`.
* `u² ∈ W` kills all residues, so `u² = c₀ + c₁u`; then `u = c₁ + c₀u⁻¹`, so `c₀ = 0`, `u ∈ Q̄`.
* `u⁻² ∈ W`: multiply by `u`, using `u/(u ∓ a) = 1 ± a/(u ∓ a)`; the residue at `0` is `−1`.
* `(u − e)⁻¹ ∈ W`: for `e = a` the residues at `±a` are `c₃α − 1` and `c₃β`, so `c₃ = 0` and
  `−1 = 0`; `e = −a, ±b` likewise; otherwise `e` is a sixth pole with residue `−1`.
-/

namespace R14_orbitExcl

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem sub_ne {u x : ℂ} (hu : u ∉ Qbar) (hx : x ∈ Qbar) : u - x ≠ 0 :=
  fun h => hu (by rw [sub_eq_zero.1 h]; exact hx)

/-- The residue at a simple pole `p` of a relation with polynomial part of degree `≤ 2` and
six simple poles `p, q₁, …, q₅` (the `qᵢ` need not be distinct, only `≠ p`) vanishes. -/
theorem residue {u c₀ c₁ c₂ d e₁ e₂ e₃ e₄ e₅ p q₁ q₂ q₃ q₄ q₅ : ℂ} (hu : u ∉ Qbar)
    (hc₀ : c₀ ∈ Qbar) (hc₁ : c₁ ∈ Qbar) (hc₂ : c₂ ∈ Qbar) (hd : d ∈ Qbar)
    (he₁ : e₁ ∈ Qbar) (he₂ : e₂ ∈ Qbar) (he₃ : e₃ ∈ Qbar) (he₄ : e₄ ∈ Qbar) (he₅ : e₅ ∈ Qbar)
    (hp : p ∈ Qbar) (hq₁ : q₁ ∈ Qbar) (hq₂ : q₂ ∈ Qbar) (hq₃ : q₃ ∈ Qbar) (hq₄ : q₄ ∈ Qbar)
    (hq₅ : q₅ ∈ Qbar) (h₁ : p ≠ q₁) (h₂ : p ≠ q₂) (h₃ : p ≠ q₃) (h₄ : p ≠ q₄) (h₅ : p ≠ q₅)
    (h : c₀ + c₁ * u + c₂ * u ^ 2 + d * (u - p)⁻¹ + e₁ * (u - q₁)⁻¹ + e₂ * (u - q₂)⁻¹ +
      e₃ * (u - q₃)⁻¹ + e₄ * (u - q₄)⁻¹ + e₅ * (u - q₅)⁻¹ = 0) : d = 0 := by
  have i0 := mul_inv_cancel₀ (sub_ne hu hp)
  have i1 := mul_inv_cancel₀ (sub_ne hu hq₁)
  have i2 := mul_inv_cancel₀ (sub_ne hu hq₂)
  have i3 := mul_inv_cancel₀ (sub_ne hu hq₃)
  have i4 := mul_inv_cancel₀ (sub_ne hu hq₄)
  have i5 := mul_inv_cancel₀ (sub_ne hu hq₅)
  lift c₀ to ↥Qbar using hc₀
  lift c₁ to ↥Qbar using hc₁
  lift c₂ to ↥Qbar using hc₂
  lift d to ↥Qbar using hd
  lift e₁ to ↥Qbar using he₁
  lift e₂ to ↥Qbar using he₂
  lift e₃ to ↥Qbar using he₃
  lift e₄ to ↥Qbar using he₄
  lift e₅ to ↥Qbar using he₅
  lift p to ↥Qbar using hp
  lift q₁ to ↥Qbar using hq₁
  lift q₂ to ↥Qbar using hq₂
  lift q₃ to ↥Qbar using hq₃
  lift q₄ to ↥Qbar using hq₄
  lift q₅ to ↥Qbar using hq₅
  have hP := aeval_eq_zero hu
    (P := (C c₀ + C c₁ * X + C c₂ * X ^ 2) * (X - C p) *
        ((X - C q₁) * (X - C q₂) * (X - C q₃) * (X - C q₄) * (X - C q₅)) +
      C d * ((X - C q₁) * (X - C q₂) * (X - C q₃) * (X - C q₄) * (X - C q₅)) +
      (X - C p) * (C e₁ * ((X - C q₂) * (X - C q₃) * (X - C q₄) * (X - C q₅)) +
        C e₂ * ((X - C q₁) * (X - C q₃) * (X - C q₄) * (X - C q₅)) +
        C e₃ * ((X - C q₁) * (X - C q₂) * (X - C q₄) * (X - C q₅)) +
        C e₄ * ((X - C q₁) * (X - C q₂) * (X - C q₃) * (X - C q₅)) +
        C e₅ * ((X - C q₁) * (X - C q₂) * (X - C q₃) * (X - C q₄)))) (by
      simp only [map_add, map_mul, map_sub, map_pow, aeval_X, aeval_C, am]
      linear_combination
        (u - p) * ((u - q₁) * (u - q₂) * (u - q₃) * (u - q₄) * (u - q₅)) * h -
        (d : ℂ) * ((u - q₁) * (u - q₂) * (u - q₃) * (u - q₄) * (u - q₅)) * i0 -
        (u - p) * e₁ * ((u - q₂) * (u - q₃) * (u - q₄) * (u - q₅)) * i1 -
        (u - p) * e₂ * ((u - q₁) * (u - q₃) * (u - q₄) * (u - q₅)) * i2 -
        (u - p) * e₃ * ((u - q₁) * (u - q₂) * (u - q₄) * (u - q₅)) * i3 -
        (u - p) * e₄ * ((u - q₁) * (u - q₂) * (u - q₃) * (u - q₅)) * i4 -
        (u - p) * e₅ * ((u - q₁) * (u - q₂) * (u - q₃) * (u - q₄)) * i5)
  have e := congrArg (aeval (p : ℂ)) hP
  simp only [map_add, map_mul, map_sub, map_pow, aeval_X, aeval_C, am, sub_self, mul_zero,
    zero_mul, add_zero, zero_add, map_zero] at e
  simpa [sub_eq_zero, h₁, h₂, h₃, h₄, h₅] using e

/-- All five residues at `0, a, −a, b, −b` of a relation vanish. -/
theorem residues {u a b c₀ c₁ c₂ r₀ r₁ r₂ r₃ r₄ : ℂ} (hu : u ∉ Qbar) (ha : a ∈ Qbar)
    (hb : b ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hc₀ : c₀ ∈ Qbar) (hc₁ : c₁ ∈ Qbar) (hc₂ : c₂ ∈ Qbar) (hr₀ : r₀ ∈ Qbar) (hr₁ : r₁ ∈ Qbar)
    (hr₂ : r₂ ∈ Qbar) (hr₃ : r₃ ∈ Qbar) (hr₄ : r₄ ∈ Qbar)
    (h : c₀ + c₁ * u + c₂ * u ^ 2 + r₀ * u⁻¹ + r₁ * (u - a)⁻¹ + r₂ * (u + a)⁻¹ +
      r₃ * (u - b)⁻¹ + r₄ * (u + b)⁻¹ = 0) :
    r₀ = 0 ∧ r₁ = 0 ∧ r₂ = 0 ∧ r₃ = 0 ∧ r₄ = 0 := by
  have z := zero_mem Qbar
  have na := neg_mem ha
  have nb := neg_mem hb
  have d1 : a ≠ -a := fun e => ha0 (by linear_combination e / 2)
  have d2 : b ≠ -b := fun e => hb0 (by linear_combination e / 2)
  have d3 : a ≠ b := fun e => hab (by rw [e])
  have d4 : a ≠ -b := fun e => hab (by rw [e, neg_sq])
  have d5 : -a ≠ b := fun e => hab (by rw [← e, neg_sq])
  have d6 : -a ≠ -b := fun e => hab (by rw [← neg_sq a, e, neg_sq])
  have n1 : (0 : ℂ) ≠ a := Ne.symm ha0
  have n2 : (0 : ℂ) ≠ -a := Ne.symm (neg_ne_zero.2 ha0)
  have n3 : (0 : ℂ) ≠ b := Ne.symm hb0
  have n4 : (0 : ℂ) ≠ -b := Ne.symm (neg_ne_zero.2 hb0)
  refine ⟨residue hu hc₀ hc₁ hc₂ hr₀ hr₁ hr₂ hr₃ hr₄ z z ha na hb nb ha n1 n2 n3 n4 n1
      (by linear_combination h), ?_, ?_, ?_, ?_⟩
  · exact residue hu hc₀ hc₁ hc₂ hr₁ hr₀ hr₂ hr₃ hr₄ z ha z na hb nb z (Ne.symm n1) d1 d3 d4
      (Ne.symm n1) (by linear_combination h)
  · exact residue hu hc₀ hc₁ hc₂ hr₂ hr₀ hr₁ hr₃ hr₄ z na z ha hb nb z (Ne.symm n2) d1.symm d5 d6
      (Ne.symm n2) (by linear_combination h)
  · exact residue hu hc₀ hc₁ hc₂ hr₃ hr₀ hr₁ hr₂ hr₄ z hb z ha na nb z (Ne.symm n3) d3.symm
      d5.symm d2 (Ne.symm n3) (by linear_combination h)
  · exact residue hu hc₀ hc₁ hc₂ hr₄ hr₀ hr₁ hr₂ hr₃ z nb z ha na hb z (Ne.symm n4) d4.symm
      d6.symm d2.symm (Ne.symm n4) (by linear_combination h)

theorem coeffs {u g₁ g₂ w : ℂ}
    (hw : w ∈ Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar,
      w = (c₁ : ℂ) + c₂ * u + c₃ * u⁻¹ + c₄ * g₁ + c₅ * g₂ := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

end R14_orbitExcl

open DiazModulus R14_orbitExcl in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (a b α β γ δ : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hα : α ∈ Qbar) (hβ : β ∈ Qbar)
    (hγ : γ ∈ Qbar) (hδ : δ ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hδ0 : δ ≠ 0) :
    LinearIndependent (↥Qbar) ![1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) ∧
      (u ^ 2)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) ∧
      ∀ e ∈ Qbar, e ≠ 0 → (u - e)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have z := zero_mem Qbar
  have o := one_mem Qbar
  have m1 := neg_mem o
  have iu := mul_inv_cancel₀ hu0
  have ia := mul_inv_cancel₀ (sub_ne hu ha)
  have ina : (u + a) * (u + a)⁻¹ = 1 := by
    have := mul_inv_cancel₀ (sub_ne hu (neg_mem ha)); rwa [sub_neg_eq_add] at this
  have ib := mul_inv_cancel₀ (sub_ne hu hb)
  have inb : (u + b) * (u + b)⁻¹ = 1 := by
    have := mul_inv_cancel₀ (sub_ne hu (neg_mem hb)); rwa [sub_neg_eq_add] at this
  have R := @residues u a b
  refine ⟨?_, fun hw => ?_, fun hw => ?_, fun e he he0 hw => ?_⟩
  · -- freeness
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_five, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, mul_one] at hg
    obtain ⟨e0, e1, e2, e3, -⟩ := R hu ha hb ha0 hb0 hab (g 0).2 (g 1).2 z (g 2).2
      (mul_mem (g 3).2 hα) (mul_mem (g 3).2 hβ) (mul_mem (g 4).2 hγ) (mul_mem (g 4).2 hδ)
      (by linear_combination hg)
    have g3 : (g 3 : ℂ) = 0 := (mul_eq_zero.1 e1).resolve_right hα0
    have g4 : (g 4 : ℂ) = 0 := (mul_eq_zero.1 e3).resolve_right hγ0
    have hr : (g 0 : ℂ) + g 1 * u = 0 := by
      rw [g3, g4, e0] at hg; linear_combination hg
    have g1 : (g 1 : ℂ) = 0 := by
      by_contra h1
      exact hu (by
        rw [show u = -(g 0 : ℂ) / g 1 by rw [eq_div_iff h1]; linear_combination hr]
        exact div_mem (neg_mem (g 0).2) (g 1).2)
    have g0 : (g 0 : ℂ) = 0 := by rw [g1] at hr; linear_combination hr
    intro i
    fin_cases i <;> exact Subtype.ext ‹_›
  · -- `u²`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e0, e1, -, e3, -⟩ := R hu ha hb ha0 hb0 hab c₁.2 c₂.2 m1 c₃.2
      (mul_mem c₄.2 hα) (mul_mem c₄.2 hβ) (mul_mem c₅.2 hγ) (mul_mem c₅.2 hδ)
      (by linear_combination -h)
    have g4 : (c₄ : ℂ) = 0 := (mul_eq_zero.1 e1).resolve_right hα0
    have g5 : (c₅ : ℂ) = 0 := (mul_eq_zero.1 e3).resolve_right hγ0
    rw [e0, g4, g5] at h
    -- `u = c₂ + c₁ u⁻¹`: the residue at `0` is `c₁`
    obtain ⟨f0, -⟩ := R hu ha hb ha0 hb0 hab c₂.2 m1 z c₁.2 z z z z
      (by linear_combination (-u⁻¹) * h + (u - c₂) * iu)
    rw [f0] at h
    have h2 : u * (u - c₂) = 0 := by linear_combination h
    exact hu (by rw [sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hu0)]; exact c₂.2)
  · -- `u⁻²`: multiply by `u`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e0, -⟩ := R hu ha hb ha0 hb0 hab
      (add_mem (add_mem c₃.2 (mul_mem c₄.2 (add_mem hα hβ))) (mul_mem c₅.2 (add_mem hγ hδ)))
      c₁.2 c₂.2 m1 (mul_mem (mul_mem c₄.2 hα) ha) (neg_mem (mul_mem (mul_mem c₄.2 hβ) ha))
      (mul_mem (mul_mem c₅.2 hγ) hb) (neg_mem (mul_mem (mul_mem c₅.2 hδ) hb))
      (by linear_combination (-u) * h + (u⁻¹ - c₃) * iu - (c₄ : ℂ) * α * ia -
            (c₄ : ℂ) * β * ina - (c₅ : ℂ) * γ * ib - (c₅ : ℂ) * δ * inb)
    exact one_ne_zero (neg_eq_zero.1 e0)
  · -- `(u − e)⁻¹`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    have hc4 := mul_mem c₄.2 hα
    have hc4' := mul_mem c₄.2 hβ
    have hc5 := mul_mem c₅.2 hγ
    have hc5' := mul_mem c₅.2 hδ
    by_cases e1 : e = a
    · rw [e1] at h
      obtain ⟨-, f1, f2, -⟩ := R hu ha hb ha0 hb0 hab c₁.2 c₂.2 z c₃.2 (sub_mem hc4 o) hc4' hc5 hc5'
        (by linear_combination -h)
      rw [(mul_eq_zero.1 f2).resolve_right hβ0] at f1
      exact one_ne_zero (by linear_combination -f1)
    by_cases e2 : e = -a
    · rw [e2, sub_neg_eq_add] at h
      obtain ⟨-, f1, f2, -⟩ := R hu ha hb ha0 hb0 hab c₁.2 c₂.2 z c₃.2 hc4 (sub_mem hc4' o) hc5 hc5'
        (by linear_combination -h)
      rw [(mul_eq_zero.1 f1).resolve_right hα0] at f2
      exact one_ne_zero (by linear_combination -f2)
    by_cases e3 : e = b
    · rw [e3] at h
      obtain ⟨-, -, -, f3, f4⟩ := R hu ha hb ha0 hb0 hab c₁.2 c₂.2 z c₃.2 hc4 hc4' (sub_mem hc5 o)
        hc5' (by linear_combination -h)
      rw [(mul_eq_zero.1 f4).resolve_right hδ0] at f3
      exact one_ne_zero (by linear_combination -f3)
    by_cases e4 : e = -b
    · rw [e4, sub_neg_eq_add] at h
      obtain ⟨-, -, -, f3, f4⟩ := R hu ha hb ha0 hb0 hab c₁.2 c₂.2 z c₃.2 hc4 hc4' hc5
        (sub_mem hc5' o) (by linear_combination -h)
      rw [(mul_eq_zero.1 f3).resolve_right hγ0] at f4
      exact one_ne_zero (by linear_combination -f4)
    -- a sixth pole
    have := residue hu c₁.2 c₂.2 z m1 c₃.2 hc4 hc4' hc5 hc5' he z ha (neg_mem ha) hb (neg_mem hb)
      he0 e1 e2 e3 e4 (by linear_combination -h)
    exact one_ne_zero (neg_eq_zero.1 this)
