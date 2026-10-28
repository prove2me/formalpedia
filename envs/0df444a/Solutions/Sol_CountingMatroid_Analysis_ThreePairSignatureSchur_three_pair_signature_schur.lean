-- Prove2me | solution 1 for CountingMatroid.Analysis.ThreePairSignatureSchur.three_pair_signature_schur
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T08:57:24.341929+00:00
-- url     : https://prove2.me/submissions/25f9920d-9f6d-42eb-b4a6-bffd1c13a6a6

import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

set_option autoImplicit false

/-!
The real quadratic signature implies the rational Schur-complement bound
used by the operational three-pair partition comparison.
-/

namespace CountingMatroid.Analysis.ThreePairSignatureSchur
end CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.ThreePairSignatureSchur

open scoped Matrix

/-- INTERNAL: Translate the real one-positive-direction signature into the
rational Schur bound, by ruling out a positive definite two-dimensional
subspace. This proves the elementary signature step rather than borrowing it.
TEXLINE: main.tex:419-449 -/
theorem solution (a c d e z : ℚ) (hc : 0 < c)
    (hsig : sigPos (threePairMatrix a c d e z).toQuadraticForm' ≤ 1) :
    ∀ x y : ℚ, 2 * c * (2 * a * x ^ 2 + 4 * d * x * y) ≤
      (z * x + 2 * e * y) ^ 2 := by
  intro x y
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  suffices h : 2 * (c : ℝ) * (2 * (a : ℝ) * (x : ℝ) ^ 2 +
      4 * (d : ℝ) * (x : ℝ) * (y : ℝ)) ≤
        ((z : ℝ) * (x : ℝ) + 2 * (e : ℝ) * (y : ℝ)) ^ 2 by
    exact_mod_cast h
  by_contra h
  have hbad := lt_of_not_ge h
  let b : ℝ := 2 * (a : ℝ) * (x : ℝ) ^ 2 +
    4 * (d : ℝ) * (x : ℝ) * (y : ℝ) -
      ((z : ℝ) * (x : ℝ) + 2 * (e : ℝ) * (y : ℝ)) ^ 2 / (2 * (c : ℝ))
  have hb : 0 < b := by
    dsimp [b]
    apply sub_pos.mpr
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith [hbad])
  let Q := (threePairMatrix a c d e z).toQuadraticForm'
  let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun u => ![u 1 * (x : ℝ),
        u 0 - u 1 * ((z : ℝ) * (x : ℝ) + 2 * (e : ℝ) * (y : ℝ)) / (2 * (c : ℝ)),
        u 1 * (y : ℝ)]
      map_add' := by intro u v; ext j; fin_cases j <;> simp <;> ring
      map_smul' := by intro s u; ext j; fin_cases j <;> simp <;> ring }
  have hcalc (u : Fin 2 → ℝ) : Q (L u) =
      2 * (c : ℝ) * (u 0) ^ 2 + b * (u 1) ^ 2 := by
    dsimp [Q, L, threePairMatrix, Matrix.toQuadraticForm', b]
    simp [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    field_simp [ne_of_gt hcR]
    <;> ring
  have hpos : (Q.comp L).PosDef := by
    intro u hu
    rw [QuadraticMap.comp_apply, hcalc]
    have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hu
      ext j
      fin_cases j <;> simp [hn]
    rcases hne with h0 | h1
    · have := sq_pos_of_ne_zero h0
      nlinarith [sq_nonneg (u 1), mul_nonneg hb.le (sq_nonneg (u 1))]
    · have := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg (u 0), mul_nonneg hcR.le (sq_nonneg (u 0))]
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro u hu
    by_contra hun
    have hp := hpos u hun
    have hz := LinearMap.mem_ker.mp hu
    simpa [QuadraticMap.comp_apply, hz] using hp
  have hrange : (Q.restrict (LinearMap.range L)).PosDef := by
    intro u hu
    obtain ⟨v, hv⟩ := u.property
    have hvne : v ≠ 0 := by
      intro hv0
      apply hu
      apply Subtype.ext
      simpa [hv0] using hv.symm
    simpa only [QuadraticMap.restrict_apply, QuadraticMap.comp_apply, hv] using hpos v hvne
  have hrank := le_sigPos_of_posDef Q hrange
  rw [LinearMap.finrank_range_of_inj hinj] at hrank
  have htwo : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [htwo] at hrank
  change 2 ≤ sigPos (threePairMatrix a c d e z).toQuadraticForm' at hrank
  omega
