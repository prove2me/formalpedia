-- Prove2me | solution 1 for DiazModulus.fv_theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:37:29.246209+00:00
-- url     : https://prove2.me/submissions/a2733842-3aac-4758-a337-f5711ed7e73c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_max_slope
import Theorems.Thm_DiazModulus_fv_semistable_core

open Complex ComplexConjugate

/-! # Waldschmidt's Theorem 2.1 of *Further variations*, for finite-dimensional `Y`

Suppose every `x · y` lies in `ℒ̃`. Since `dim X = d > n`, `n ≥ 1`. Choose a ℂ-subspace `W₀ ≠ 0` of
maximal slope for `X` and put `n₀ = dim W₀`, `X₀ = X ∩ W₀`, `d₀ = dim X₀`. Maximality gives
`n₀·dim(X ∩ W) ≤ d₀·dim W` for every `W`; at `W = ℂⁿ` this is `d·n₀ ≤ d₀·n`, so `d₀ > n₀`, and since
`X₀ ∩ W ⊂ X ∩ W`, `X₀` is semistable in `W₀`. The semistable case applied to `W₀`, `X₀` and `Y` gives
`V ≠ ℂⁿ` with `(d₀ − n₀)·ρ ≤ d₀·c`, where `ρ = dim Y − dim(Y ∩ V)` and `c = n − dim V`; the hypothesis
at the same `V` says `d·c < (d − n)·ρ`. Multiplying the first by `d` and the second by `d₀`
gives `ρ·(d·n₀ − d₀·n) > 0`, which is impossible because `d·n₀ ≤ d₀·n`. -/

namespace RC3_T21
open DiazModulus

/-- The final arithmetic, with `d = n + a` and `d₀ = n₀ + b`. -/
theorem arith (n a n₀ b c ρ : ℕ) (hb : 0 < n₀ + b)
    (H1 : (n + a) * c < a * ρ) (H2 : b * ρ ≤ (n₀ + b) * c) (H3 : (n + a) * n₀ ≤ (n₀ + b) * n) :
    False := by
  have e1 := Nat.mul_lt_mul_of_pos_left H1 hb
  have e2 := Nat.mul_le_mul_left (n + a) H2
  have e3 := Nat.mul_le_mul_right ρ H3
  nlinarith [e1, e2, e3]

end RC3_T21

open DiazModulus RC3_T21 in
theorem solution {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] [FiniteDimensional (↥Qbar) ↥Y]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) <
        (Module.finrank (↥Qbar) ↥X - n) *
          (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)))) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  by_contra hne
  push Not at hne
  have hn : 0 < n := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    subst h0
    have hX : X = ⊥ := Subsingleton.elim _ _
    rw [hX, finrank_bot] at hdn
    exact Nat.lt_irrefl 0 hdn
  obtain ⟨W₀, hW₀, hmax⟩ := DiazModulus.fv_max_slope hn X
  have hn₀ : 0 < Module.finrank ℂ ↥W₀ := Submodule.one_le_finrank_iff.mpr hW₀
  -- `X₀ = X ∩ W₀` is semistable in `W₀`
  have hss : ∀ W : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ ↥W₀ *
          Module.finrank (↥Qbar) ↥((X ⊓ W₀.restrictScalars (↥Qbar)) ⊓ W.restrictScalars (↥Qbar)) ≤
        Module.finrank (↥Qbar) ↥(X ⊓ W₀.restrictScalars (↥Qbar)) * Module.finrank ℂ ↥W := by
    intro W
    have hle : (X ⊓ W₀.restrictScalars (↥Qbar)) ⊓ W.restrictScalars (↥Qbar) ≤
        X ⊓ W.restrictScalars (↥Qbar) := inf_le_inf_right _ inf_le_left
    rw [mul_comm]
    exact (Nat.mul_le_mul_right _ (Submodule.finrank_mono hle)).trans (hmax W)
  -- the slope inequality at `W = ℂⁿ`
  have htop := hmax ⊤
  rw [Submodule.restrictScalars_top, inf_top_eq, finrank_top, Module.finrank_fin_fun] at htop
  have hd₀ : Module.finrank ℂ ↥W₀ < Module.finrank (↥Qbar) ↥(X ⊓ W₀.restrictScalars (↥Qbar)) := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul_right n hle
    have := Nat.mul_lt_mul_of_pos_left hdn hn₀
    nlinarith
  obtain ⟨V, hV, hcore⟩ := DiazModulus.fv_semistable_core W₀ (X ⊓ W₀.restrictScalars (↥Qbar)) Y
    (fun x hx => hx.2) hss hd₀ (fun x hx y hy => hne x hx.1 y hy)
  have hH := hμ V hV
  generalize Module.finrank (↥Qbar) ↥X = d at *
  generalize Module.finrank (↥Qbar) ↥(X ⊓ W₀.restrictScalars (↥Qbar)) = d₀ at *
  generalize Module.finrank ℂ ↥W₀ = n₀ at *
  generalize Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)) = ρ
    at *
  generalize n - Module.finrank ℂ ↥V = c at *
  obtain ⟨a, rfl⟩ : ∃ a, d = n + a := ⟨d - n, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, d₀ = n₀ + b := ⟨d₀ - n₀, by omega⟩
  rw [Nat.add_sub_cancel_left] at hH hcore
  exact arith n a n₀ b c ρ (by omega) hH hcore htop
