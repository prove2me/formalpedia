-- Prove2me | solution 1 for GNFS.finrank_adjoin_root_eq_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:49:43.642232+00:00
-- url     : https://prove2.me/submissions/7141f974-2199-4348-86b8-ba81c52223c9

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

theorem solution (f : ℚ[X]) (hf : Irreducible f) (θ : ℂ)
    (hθ : aeval θ f = 0) :
    Module.finrank ℚ ℚ⟮θ⟯ = f.natDegree := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hint : IsIntegral ℚ θ := ⟨f * C f.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hf0, by
    rw [eval₂_mul, eval₂_C]
    have : eval₂ (algebraMap ℚ ℂ) θ f = 0 := hθ
    rw [this, zero_mul]⟩
  rw [adjoin.finrank hint, ← minpoly.eq_of_irreducible hf hθ,
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hf0))]
