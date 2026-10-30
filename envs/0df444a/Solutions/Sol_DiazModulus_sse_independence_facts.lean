-- Prove2me | solution 1 for DiazModulus.sse_independence_facts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:55.791986+00:00
-- url     : https://prove2.me/submissions/6fd7a352-a894-4baa-8107-00337ca12503

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Two independence facts for the strong six exponentials setup

First fact: if `Σ_{(a,j)} s_{aj} ω_a y_j = 0` with integers `s`, group the sum by `j`. The
coefficient `Σ_a s_{aj} ω_a` of `y_j` is algebraic (integers and the algebraic `ω_a` lie in the
subfield `Q̄`), so the `Q̄`-independence of `y` makes every coefficient vanish, and then the
ℚ-independence of `ω` makes every `s_{aj}` vanish.

Second fact: let `c x_i = β v_i` with `v ∈ Q̄²` and `β ≠ 0`, and suppose `c ≠ 0`. The relation
`v_1 x_0 − v_0 x_1 = 0` holds (multiply by `c` and use the hypothesis), so the `Q̄`-independence
of `x` forces `v = 0`; then `c x_0 = 0`, so `x_0 = 0`, which an independent family cannot have. -/

namespace C14_S2
open DiazModulus

theorem int_comb_mem (m : ℕ) (ω : Fin m → ℂ) (hωalg : ∀ a, ω a ∈ Qbar) (t : Fin m → ℤ) :
    ∑ a, (t a : ℂ) * ω a ∈ Qbar :=
  Qbar.sum_mem (fun a _ => Qbar.mul_mem (Qbar.intCast_mem _) (hωalg a))

end C14_S2

open DiazModulus C14_S2 in
theorem solution (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y) :
    (∀ s : Fin m × Fin 3 → ℤ, ∑ p, (s p : ℂ) * ω p.1 * y p.2 = 0 → s = 0) ∧
    ∀ (β c : ℂ) (v : Fin 2 → ℂ), β ≠ 0 → (∀ i, v i ∈ Qbar) → (∀ i, c * x i = β * v i) → c = 0 := by
  refine ⟨fun s hs => ?_, fun β c v hβ hv hcx => ?_⟩
  · -- group by `j` and use the independence of `y`
    have hy' := Fintype.linearIndependent_iff.mp hy
      (fun j => ⟨∑ a, (s (a, j) : ℂ) * ω a, int_comb_mem m ω hωalg _⟩) (by
        rw [Fintype.sum_prod_type, Finset.sum_comm] at hs
        rw [← hs]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Subfield.smul_def, smul_eq_mul, Finset.sum_mul])
    funext ⟨a, j⟩
    have hj : ∑ a, (s (a, j) : ℂ) * ω a = 0 := by
      have := hy' j
      simpa [Subtype.ext_iff] using this
    have hω' := Fintype.linearIndependent_iff.mp hωQ (fun a => (s (a, j) : ℚ)) (by
      rw [← hj]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Rat.smul_def, Rat.cast_intCast])
    exact_mod_cast hω' a
  · by_contra hc
    have hrel := Fintype.linearIndependent_iff.mp hx
      ![⟨v 1, hv 1⟩, ⟨-v 0, Qbar.neg_mem (hv 0)⟩] (by
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Subfield.smul_def, smul_eq_mul]
        apply mul_left_cancel₀ hc
        have h0 := hcx 0
        have h1 := hcx 1
        linear_combination (v 1) * h0 - (v 0) * h1)
    have hv0 : v 0 = 0 := by
      have := hrel 1
      simp only [Matrix.cons_val_one, Subtype.ext_iff] at this
      simpa using this
    have hx0 : x 0 = 0 := by
      have := hcx 0
      rw [hv0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hc
    exact hx.ne_zero 0 hx0
