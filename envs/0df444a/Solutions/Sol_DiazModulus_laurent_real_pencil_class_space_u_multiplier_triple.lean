-- Prove2me | solution 1 for DiazModulus.laurent_real_pencil_class_space_u_multiplier_triple
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:56:04.841046+00:00
-- url     : https://prove2.me/submissions/aad9b506-db47-45ba-bd07-7309ce488925

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_real_pencil_normal_form_carries_two_by_three_configuration

open Complex ComplexConjugate

/-! # A Laurent real-pencil class space carries a `u`-multiplier triple

Let `u ∉ Q̄` with `u ū = s²`, `s ∈ Q̄`, put `v = u/s` and `g = G(v) + κ·conj(v G(v))` with `|κ| = 1` and
`deg G ≥ 1`. Then `t = (u⁻¹, 1, g)` is a `Q̄`-free triple in `W = span(1, u, ū, g, ḡ)` with `u·t ⊆ W`.

First `s` is real: `s² = |u|² > 0` forces `Im s = 0`. Hence `v v̄ = 1`, `v ∉ Q̄`, and `u⁻¹ = s⁻¹ v̄`.
Freeness: the real-pencil normal form node (10.92) makes `(v̄, 1, g)` free; scaling the first vector by
`s⁻¹ ∈ Q̄ˣ` gives `(u⁻¹, 1, g)`. Membership: `u⁻¹ = (s²)⁻¹ ū`, `1` and `g` lie in `W`.
Multipliers: `u·u⁻¹ = 1`, `u·1 = u`, and `v g = v G(v) + κ v v̄ conj G(v) = κ ḡ` because `v v̄ = κ κ̄ = 1`,
so `u g = s κ ḡ ∈ W`.
-/

namespace R21a_B3
open DiazModulus

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := by
  rintro rfl; exact hu Qbar.zero_mem

/-- `s² = u ū` with `u ≠ 0` makes `s` real. -/
theorem conj_s {u s : ℂ} (hu0 : u ≠ 0) (hss : s * s = u * conj u) : conj s = s := by
  have h1 : (s * s).im = 0 := by rw [hss, Complex.mul_conj]; simp
  have h2 : 0 < (s * s).re := by
    rw [hss, Complex.mul_conj]; simpa using Complex.normSq_pos.2 hu0
  simp only [Complex.mul_im, Complex.mul_re] at h1 h2
  have him : s.im = 0 := by
    by_contra h
    have hre : s.re = 0 := by
      have : s.re * s.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · exact absurd h' h
    rw [hre] at h2; nlinarith [sq_nonneg s.im]
  exact Complex.conj_eq_iff_im.2 him

theorem li3 (v : Fin 3 → ℂ)
    (h : ∀ a b c : ↥Qbar, (a : ℂ) * v 0 + b * v 1 + c * v 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    LinearIndependent (↥Qbar) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul] at hg
  obtain ⟨h0, h1, h2⟩ := h _ _ _ hg
  intro i; fin_cases i <;> assumption

theorem li3_use {v : Fin 3 → ℂ} (hv : LinearIndependent (↥Qbar) v) (a b c : ↥Qbar)
    (h : (a : ℂ) * v 0 + b * v 1 + c * v 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have := Fintype.linearIndependent_iff.1 hv ![a, b, c]
    (by simpa [Fin.sum_univ_three, Subfield.smul_def] using h)
  exact ⟨this 0, this 1, this 2⟩

end R21a_B3

open DiazModulus R21a_B3 in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (κ : ℂ) (hκ : κ ∈ Qbar) (hκ1 : κ * conj κ = 1) (G : Polynomial ↥Qbar) (hG : 1 ≤ G.natDegree) :
    LinearIndependent (↥Qbar) ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] ∧
      ∀ j, ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] j ∈
        Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ) ∧
        u * ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] j ∈
        Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hsr := conj_s hu0 hss
  have hs0 : s ≠ 0 := by
    rintro rfl; exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  set v := u / s with hv_def
  have hvQ : v ∉ Qbar := by
    intro h; apply hu
    have : u = v * s := by rw [hv_def]; field_simp
    rw [this]; exact Qbar.mul_mem h hs
  have hcv : conj v = conj u / s := by rw [hv_def, map_div₀, hsr]
  have hv1 : v * conj v = 1 := by
    rw [hcv, hv_def]; field_simp; linear_combination -hss
  obtain ⟨-, hli, -⟩ :=
    DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration v hvQ hv1 κ hκ hκ1 G hG
  set A := Polynomial.aeval v G
  set g := A + κ * conj (v * A) with hg_def
  set W := Submodule.span Qbar ({1, u, conj u, g, conj g} : Set ℂ)
  have hinv : u⁻¹ = s⁻¹ * conj v := by
    rw [hcv]; field_simp; linear_combination hss
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mu : u ∈ W := Submodule.subset_span (by simp)
  have mcu : conj u ∈ W := Submodule.subset_span (by simp)
  have mg : g ∈ W := Submodule.subset_span (by simp)
  have mcg : conj g ∈ W := Submodule.subset_span (by simp)
  have hsQ : s * s ∈ Qbar := Qbar.mul_mem hs hs
  have hκ' : s * κ ∈ Qbar := Qbar.mul_mem hs hκ
  have mui : u⁻¹ ∈ W := by
    have : u⁻¹ = ((⟨s * s, hsQ⟩ : ↥Qbar)⁻¹ : ↥Qbar) • conj u := by
      rw [Subfield.smul_def, Subfield.coe_inv]
      show u⁻¹ = (s * s)⁻¹ * conj u
      rw [hss, mul_inv, mul_assoc, inv_mul_cancel₀ hcu0, mul_one]
    rw [this]; exact W.smul_mem _ mcu
  have hvg : v * g = κ * conj g := by
    rw [hg_def]; simp only [map_add, map_mul, Complex.conj_conj]
    linear_combination (κ * conj A) * hv1 - (v * A) * hκ1
  have mug : u * g ∈ W := by
    have : u * g = (⟨s * κ, hκ'⟩ : ↥Qbar) • conj g := by
      rw [Subfield.smul_def]
      have hu' : u = s * v := by rw [hv_def]; field_simp
      simp only; rw [hu', mul_assoc, hvg]; ring
    rw [this]; exact W.smul_mem _ mcg
  refine ⟨li3 _ fun a b c h => ?_, fun j => ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    have hs' : (⟨s, hs⟩ : ↥Qbar) ≠ 0 := fun h0 => hs0 (congrArg Subtype.val h0)
    obtain ⟨h0, h1, h2⟩ := li3_use hli (a * (⟨s, hs⟩ : ↥Qbar)⁻¹) b c (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Subfield.coe_mul, Subfield.coe_inv]
      rw [hinv] at h; linear_combination h)
    exact ⟨by simpa [hs'] using h0, h1, h2⟩
  · fin_cases j
    · refine ⟨mui, ?_⟩; simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [mul_inv_cancel₀ hu0]; exact m1
    · refine ⟨m1, ?_⟩; simpa using mu
    · exact ⟨mg, mug⟩
