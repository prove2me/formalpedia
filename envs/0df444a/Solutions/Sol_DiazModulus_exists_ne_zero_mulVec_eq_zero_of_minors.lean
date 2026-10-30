-- Prove2me | solution 1 for DiazModulus.exists_ne_zero_mulVec_eq_zero_of_minors
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:17:54.609017+00:00
-- url     : https://prove2.me/submissions/d02108d5-662d-4fec-9799-d1bd6e31ae58

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A matrix with all maximal minors zero has a non-zero kernel vector

Let `M` be a `ρ × γ` matrix over a field with every `γ × γ` minor `det (M.submatrix f id)` zero.
Suppose no non-zero `c` has `M c = 0`. Then `c ↦ M c` is injective, so `rank M = |γ|`, and by
`Matrix.rank_eq_finrank_span_row` the rows of `M` span a space of dimension `|γ|`. By
`exists_linearIndependent'` some injectively indexed subfamily of rows is linearly independent
with the same span; it therefore has exactly `|γ|` members (`finrank_span_eq_card`). Reindexing
it by `γ` gives `f : γ → ρ` whose square submatrix has linearly independent rows, hence is
invertible (`Matrix.linearIndependent_rows_iff_isUnit`), so its determinant is non-zero:
a contradiction.
-/

namespace C14_A11
open DiazModulus
end C14_A11

open DiazModulus C14_A11 in
theorem solution {K ρ γ : Type*} [Field K] [Fintype ρ] [Fintype γ] [DecidableEq γ]
    (M : Matrix ρ γ K) (hM : ∀ f : γ → ρ, (M.submatrix f id).det = 0) :
    ∃ c : γ → K, c ≠ 0 ∧ M.mulVec c = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    exact hcon c hne hc
  have hrank : M.rank = Fintype.card γ := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K M.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card γ := by
    rw [← finrank_span_eq_card hli, hspan, hrank]
  let e : γ ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hli' : LinearIndependent K (M.submatrix (a ∘ e) id).row := by
    have := hli.comp e e.injective
    exact this
  have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero (hM (a ∘ e))
