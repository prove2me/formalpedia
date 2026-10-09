-- Prove2me | solution 1 for DiazModulus.polynomial_submodule_trailing_degrees_card
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T19:20:10.235772+00:00
-- url     : https://prove2.me/submissions/ac9d3c51-4365-4d7a-bfdb-eb7ddc5f4fc6

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# Trailing degrees of a finite-dimensional space of polynomials

For a finite-dimensional `K`-subspace `X` of `K[X]`, the set of trailing degrees (orders at `0`)
of its non-zero elements has exactly `dim X` elements.

Induction on `dim X`. If `X = 0` the set is empty. Otherwise let `n₀` be the least trailing
degree, attained by some `f₀ ∈ X`. Put `X' = X ∩ ker (f ↦ coeff f n₀)`. Then `X = X' + K f₀` and
`X' ∩ K f₀ = 0` (the coefficient of `f₀` at `n₀` is its trailing coefficient, non-zero), so
`dim X' = dim X - 1`. An element of `X` with trailing degree `n > n₀` has zero coefficient at
`n₀`, so lies in `X'`; an element of `X'` never has trailing degree `n₀`. Hence the trailing
degrees of `X` are those of `X'` together with the new value `n₀`, and the count goes up by one.
-/

namespace R6_trailDeg

open Polynomial

variable {K : Type*} [Field K]

/-- The set of trailing degrees of the non-zero elements of `X`. -/
noncomputable abbrev tds (X : Submodule K K[X]) : Set ℕ :=
  natTrailingDegree '' ((X : Set K[X]) \ {0})

theorem coeff_ntd_ne_zero {f : K[X]} (hf : f ≠ 0) : f.coeff f.natTrailingDegree ≠ 0 :=
  fun h => hf (trailingCoeff_eq_zero.mp h)

theorem key (n : ℕ) : ∀ (X : Submodule K K[X]) [FiniteDimensional K X],
    Module.finrank K X = n → (tds X).Finite ∧ (tds X).ncard = n := by
  induction n with
  | zero =>
    intro X _ hX
    have : X = ⊥ := Submodule.finrank_eq_zero.mp hX
    subst this
    have : tds (⊥ : Submodule K K[X]) = ∅ := by
      ext m; simp [tds]
    rw [this]; exact ⟨Set.finite_empty, Set.ncard_empty _⟩
  | succ n ih =>
    intro X _ hX
    have hXne : X ≠ ⊥ := by
      intro h; subst h; simp at hX
    obtain ⟨f, hfX, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    have hSne : (tds X).Nonempty := ⟨_, f, ⟨hfX, hf0⟩, rfl⟩
    set n₀ := sInf (tds X) with hn₀
    obtain ⟨f₀, ⟨hf₀X, hf₀0⟩, hf₀n⟩ := Nat.sInf_mem hSne
    rw [← hn₀] at hf₀n
    have hc₀ : f₀.coeff n₀ ≠ 0 := hf₀n ▸ coeff_ntd_ne_zero (Set.mem_singleton_iff.not.mp hf₀0)
    have hf₀0' : f₀ ≠ 0 := Set.mem_singleton_iff.not.mp hf₀0
    set X' : Submodule K K[X] := X ⊓ LinearMap.ker (lcoeff K n₀) with hX'
    have memX' : ∀ g, g ∈ X' ↔ g ∈ X ∧ g.coeff n₀ = 0 := by
      intro g; simp [hX', Submodule.mem_inf, LinearMap.mem_ker]
    have : FiniteDimensional K X' := Submodule.finiteDimensional_of_le inf_le_left
    have hsup : X' ⊔ K ∙ f₀ = X := by
      apply le_antisymm (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hf₀X))
      intro g hg
      rw [Submodule.mem_sup]
      refine ⟨g - (g.coeff n₀ / f₀.coeff n₀) • f₀, ?_, (g.coeff n₀ / f₀.coeff n₀) • f₀,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
      rw [memX']
      refine ⟨X.sub_mem hg (X.smul_mem _ hf₀X), ?_⟩
      rw [coeff_sub, coeff_smul, smul_eq_mul, div_mul_cancel₀ _ hc₀, sub_self]
    have hinf : X' ⊓ K ∙ f₀ = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Submodule.mem_inf, memX', Submodule.mem_span_singleton] at hg
      obtain ⟨⟨_, hg0⟩, c, rfl⟩ := hg
      rw [coeff_smul, smul_eq_mul, mul_eq_zero] at hg0
      rcases hg0 with h | h
      · simp [h]
      · exact absurd h hc₀
    have hdim : Module.finrank K X' = n := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq X' (K ∙ f₀)
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hf₀0', hX] at h
      omega
    obtain ⟨hfin, hcard⟩ := ih X' hdim
    have hnot : n₀ ∉ tds X' := by
      rintro ⟨g, ⟨hgX', hg0⟩, hgn⟩
      have hg0' : g ≠ 0 := Set.mem_singleton_iff.not.mp hg0
      exact coeff_ntd_ne_zero hg0' (hgn ▸ ((memX' g).mp hgX').2)
    have heq : tds X = insert n₀ (tds X') := by
      ext m
      constructor
      · rintro ⟨g, ⟨hgX, hg0⟩, rfl⟩
        by_cases hm : g.natTrailingDegree = n₀
        · exact Or.inl hm
        · right
          refine ⟨g, ⟨(memX' g).mpr ⟨hgX, ?_⟩, hg0⟩, rfl⟩
          apply coeff_eq_zero_of_lt_natTrailingDegree
          exact lt_of_le_of_ne (Nat.sInf_le ⟨g, ⟨hgX, hg0⟩, rfl⟩) (Ne.symm hm)
      · rintro (rfl | ⟨g, ⟨hgX', hg0⟩, rfl⟩)
        · exact ⟨f₀, ⟨hf₀X, hf₀0⟩, hf₀n⟩
        · exact ⟨g, ⟨((memX' g).mp hgX').1, hg0⟩, rfl⟩
    rw [heq]
    exact ⟨hfin.insert n₀, by rw [Set.ncard_insert_of_notMem hnot hfin, hcard]⟩

end R6_trailDeg

open DiazModulus R6_trailDeg in
theorem solution (K : Type*) [Field K]
    (X : Submodule K (Polynomial K)) [FiniteDimensional K X] :
    (Polynomial.natTrailingDegree '' ((X : Set (Polynomial K)) \ {0})).ncard =
      Module.finrank K X :=
  (key (Module.finrank K X) X rfl).2
