-- Prove2me | solution 1 for Freiman.legendre_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:17.823977+00:00
-- url     : https://prove2.me/submissions/f772be26-82cb-475a-bbd7-e5207156c085

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_rational_cf_finite_expansion
import Theorems.Thm_Freiman_legendre_adjacent_cylinders
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_prefixEval_zero

open Freiman

theorem solution (b : ℕ → ℕ+) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) :
    |cfValue b - (p : ℝ) / q| < 1 / (2 * (q : ℝ)^2) →
      ∃ n : ℕ, cfConvergent b n = (p : ℝ) / q := by
  intro h
  obtain ⟨w, hw, hl, hpw, hqw⟩ := rational_cf_finite_expansion p q hp hpq hcop
  have hv : finiteCF w = (p : ℝ) / q := by
    have hm := prefixEval_mobius w 0 (le_refl 0)
    simpa [prefixEval_zero, hpw, hqw] using hm
  have he := legendre_adjacent_cylinders w hw hl b
  rw [hv, hqw] at he
  exact he h
