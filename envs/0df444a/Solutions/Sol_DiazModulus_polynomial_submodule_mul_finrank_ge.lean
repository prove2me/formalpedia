-- Prove2me | solution 1 for DiazModulus.polynomial_submodule_mul_finrank_ge
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T19:16:26.896995+00:00
-- url     : https://prove2.me/submissions/943fba6d-39ad-446e-ab88-870aaa314bfd

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_polynomial_submodule_trailing_degrees_card

open Complex ComplexConjugate

/-!
# Dimension of a product of two spaces of polynomials

For non-zero finite-dimensional `K`-subspaces `X, Y` of `K[X]`,
`dim X + dim Y ≤ dim (X * Y) + 1`.

Let `A, B, C` be the sets of trailing degrees of the non-zero elements of `X`, `Y` and `X * Y`;
by `polynomial_submodule_trailing_degrees_card` their cardinalities are the three dimensions
(`X * Y` is finite-dimensional since `X, Y` are finitely generated, `Submodule.FG.mul`). In
particular `A, B, C` are finite and `A, B` are non-empty. For non-zero `f ∈ X`, `g ∈ Y` the
product `f g` is a non-zero element of `X * Y` with trailing degree `ord f + ord g`, so
`A + B ⊆ C`. The Cauchy–Davenport inequality in the linearly ordered cancellative monoid `ℕ`
(`cauchy_davenport_add_of_linearOrder_isCancelAdd`) gives `|A| + |B| - 1 ≤ |A + B| ≤ |C|`.
-/

namespace R6_mulFinrank

open Polynomial Pointwise

/-- Cauchy–Davenport for finite non-empty sets of naturals, in `ncard` form. -/
theorem ncard_add_le {A B C : Set ℕ} (hA : A.Finite) (hB : B.Finite) (hC : C.Finite)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hsub : A + B ⊆ C) :
    A.ncard + B.ncard ≤ C.ncard + 1 := by
  have hAne' : hA.toFinset.Nonempty := by simpa using hAne
  have hBne' : hB.toFinset.Nonempty := by simpa using hBne
  have hCD := cauchy_davenport_add_of_linearOrder_isCancelAdd hAne' hBne'
  have hsub' : ((hA.toFinset + hB.toFinset : Finset ℕ) : Set ℕ) ⊆ C := by
    rw [Finset.coe_add, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset]
    exact hsub
  have hle := Set.ncard_le_ncard hsub' hC
  rw [Set.ncard_coe_finset] at hle
  rw [Set.ncard_eq_toFinset_card _ hA, Set.ncard_eq_toFinset_card _ hB]
  have : 0 < hA.toFinset.card := hAne'.card_pos
  omega

variable {K : Type*} [Field K]

/-- The set of trailing degrees of the non-zero elements of `X`. -/
noncomputable abbrev tds (X : Submodule K K[X]) : Set ℕ :=
  natTrailingDegree '' ((X : Set K[X]) \ {0})

theorem tds_ncard (X : Submodule K K[X]) [FiniteDimensional K X] :
    (tds X).ncard = Module.finrank K X :=
  DiazModulus.polynomial_submodule_trailing_degrees_card K X

theorem tds_finite (X : Submodule K K[X]) [FiniteDimensional K X] (hX : X ≠ ⊥) :
    (tds X).Finite := by
  apply Set.finite_of_ncard_ne_zero
  rw [tds_ncard]
  intro h
  exact hX (Submodule.finrank_eq_zero.mp h)

theorem tds_nonempty (X : Submodule K K[X]) (hX : X ≠ ⊥) : (tds X).Nonempty := by
  obtain ⟨f, hfX, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  exact ⟨_, f, ⟨hfX, hf0⟩, rfl⟩

theorem tds_add_subset (X Y : Submodule K K[X]) : tds X + tds Y ⊆ tds (X * Y) := by
  rintro _ ⟨_, ⟨f, ⟨hfX, hf0⟩, rfl⟩, _, ⟨g, ⟨hgY, hg0⟩, rfl⟩, rfl⟩
  have hf : f ≠ 0 := hf0
  have hg : g ≠ 0 := hg0
  exact ⟨f * g, ⟨Submodule.mul_mem_mul hfX hgY, mul_ne_zero hf hg⟩, natTrailingDegree_mul hf hg⟩

end R6_mulFinrank

open DiazModulus R6_mulFinrank in
theorem solution (K : Type*) [Field K]
    (X Y : Submodule K (Polynomial K)) [FiniteDimensional K X] [FiniteDimensional K Y]
    (hX : X ≠ ⊥) (hY : Y ≠ ⊥) :
    Module.finrank K X + Module.finrank K Y ≤ Module.finrank K ↥(X * Y) + 1 := by
  have hXfg : X.FG := (Submodule.fg_iff_finiteDimensional X).mpr inferInstance
  have hYfg : Y.FG := (Submodule.fg_iff_finiteDimensional Y).mpr inferInstance
  have : FiniteDimensional K ↥(X * Y) :=
    (Submodule.fg_iff_finiteDimensional _).mp (Submodule.FG.mul hXfg hYfg)
  have hXY : X * Y ≠ ⊥ := by
    obtain ⟨f, hfX, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
    obtain ⟨g, hgY, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    intro h
    have : f * g ∈ X * Y := Submodule.mul_mem_mul hfX hgY
    rw [h, Submodule.mem_bot] at this
    exact mul_ne_zero hf0 hg0 this
  have hA := tds_finite X hX
  have hB := tds_finite Y hY
  have hC := tds_finite (X * Y) hXY
  have h := ncard_add_le hA hB hC (tds_nonempty X hX) (tds_nonempty Y hY) (tds_add_subset X Y)
  rwa [tds_ncard, tds_ncard, tds_ncard] at h
