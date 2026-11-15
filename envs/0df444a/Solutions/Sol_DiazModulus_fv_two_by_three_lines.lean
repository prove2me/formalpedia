-- Prove2me | solution 1 for DiazModulus.fv_two_by_three_lines
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:37:32.111103+00:00
-- url     : https://prove2.me/submissions/3a77d153-52cf-4910-9adc-3bd2f6ad6e25

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Lines meet the column space of `(I₂, M)` in dimension at most three

Let `X` be the `Q̄`-span of the five columns `e₁, e₂, (M₀ⱼ, M₁ⱼ)` of `(I₂, M)`, so `dim X ≤ 5`. A proper
`ℂ`-subspace `V` of `ℂ²` lies in the kernel of a non-zero `ℂ`-linear form `p`, `p(z) = s₀z₀ + s₁z₁`. By
rank–nullity for the `Q̄`-linear map `p` restricted to `X`, `dim(X ∩ V) ≤ dim(X ∩ ker p) = dim X − dim p(X)`,
so it suffices that `dim_Q̄ p(X) ≥ 2`. Otherwise `p(X) = Q̄·c`, and `s₀ = a₀c`, `s₁ = a₁c`,
`s₀M₀ⱼ + s₁M₁ⱼ = bⱼc` with algebraic `a, b`. Then `c ≠ 0` (as `s ≠ 0`), and dividing by `c` gives
`a₀M₀ⱼ + a₁M₁ⱼ − bⱼ = 0` for `j = 0, 1, 2`: the relation `a₀·(row 0) + a₁·(row 1) − Σⱼ bⱼeⱼ = 0` among
the five rows of `(M; I₃)`. These rows are `Q̄`-free, so `a₀ = a₁ = 0`, hence `s = 0`, a contradiction. -/

namespace RC3_A6
open DiazModulus

theorem dual_two (f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) (z : Fin 2 → ℂ) :
    f z = z 0 * f (Pi.single 0 1) + z 1 * f (Pi.single 1 1) := by
  conv_lhs => rw [show z = z 0 • Pi.single 0 1 + z 1 • Pi.single 1 1 by
    ext i; fin_cases i <;> simp]
  simp [map_add, map_smul]

theorem col_inl (M : Matrix (Fin 2) (Fin 3) ℂ) (i : Fin 2) :
    (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col (Sum.inl i) = Pi.single i 1 := by
  ext k; simp [Matrix.one_apply, Pi.single_apply]

theorem col_inr (M : Matrix (Fin 2) (Fin 3) ℂ) (j : Fin 3) :
    (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col (Sum.inr j) = fun i => M i j := by
  ext k; simp

end RC3_A6

open DiazModulus RC3_A6 in
theorem solution (M : Matrix (Fin 2) (Fin 3) ℂ)
    (hrows : LinearIndependent (↥Qbar) (Matrix.fromRows M (1 : Matrix (Fin 3) (Fin 3) ℂ)).row)
    (V : Submodule ℂ (Fin 2 → ℂ)) (hV : V ≠ ⊤) :
    Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar)
        (Set.range (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) ⊓
          V.restrictScalars (↥Qbar)) ≤ 3 := by
  set v := (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col with hv
  set X := Submodule.span (↥Qbar) (Set.range v) with hX
  have : FiniteDimensional (↥Qbar) X := FiniteDimensional.span_of_finite _ (Set.finite_range v)
  obtain ⟨f, hf0, hfV⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hV) inferInstance
  have hVf : V ≤ LinearMap.ker f := LinearMap.le_ker_iff_map.mpr hfV
  set f' : (Fin 2 → ℂ) →ₗ[↥Qbar] ℂ := (f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).restrictScalars (↥Qbar) with hf'
  set g := f'.domRestrict X with hg
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_domRestrict] at h1
  have hX5 : Module.finrank (↥Qbar) X ≤ 5 := (finrank_range_le_card (R := ↥Qbar) v).trans (by simp)
  have hker : Module.finrank (↥Qbar) ↥(X ⊓ V.restrictScalars (↥Qbar)) ≤
      Module.finrank (↥Qbar) (LinearMap.ker g) := by
    rw [hg, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
      Submodule.map_comap_subtype]
    exact Submodule.finrank_mono (inf_le_inf_left _ fun x hx => hVf hx)
  -- the two coordinates of the form
  set s0 := f (Pi.single 0 1) with hs0
  set s1 := f (Pi.single 1 1) with hs1
  have hs : ¬ (s0 = 0 ∧ s1 = 0) := by
    rintro ⟨h0, h1⟩; apply hf0; refine LinearMap.ext fun z => ?_
    rw [dual_two f z, ← hs0, ← hs1, h0, h1]; simp
  have hrange : 2 ≤ Module.finrank (↥Qbar) ↥(X.map f') := by
    by_contra hlt
    have hle : Module.finrank (↥Qbar) ↥(X.map f') ≤ 1 := by omega
    rw [Submodule.finrank_le_one_iff_isPrincipal] at hle
    obtain ⟨⟨c, hc⟩⟩ := hle
    have hmem : ∀ k, ∃ a : ↥Qbar, (a : ℂ) * c = f (v k) := fun k => by
      have hk : f' (v k) ∈ X.map f' := Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
      rw [hc, Submodule.mem_span_singleton] at hk
      obtain ⟨a, ha⟩ := hk
      exact ⟨a, by rw [Subfield.smul_def, smul_eq_mul] at ha; exact ha⟩
    choose a ha using hmem
    have ha0 : (a (Sum.inl 0) : ℂ) * c = s0 := by rw [ha, hv, col_inl]
    have ha1 : (a (Sum.inl 1) : ℂ) * c = s1 := by rw [ha, hv, col_inl]
    have hb : ∀ j, (a (Sum.inr j) : ℂ) * c = M 0 j * s0 + M 1 j * s1 := fun j => by
      rw [ha, hv, col_inr, dual_two]
    have hc0 : c ≠ 0 := by
      rintro rfl; exact hs ⟨by rw [← ha0, mul_zero], by rw [← ha1, mul_zero]⟩
    have key : ∀ j, (a (Sum.inl 0) : ℂ) * M 0 j + a (Sum.inl 1) * M 1 j - a (Sum.inr j) = 0 :=
      fun j => by
        apply mul_left_cancel₀ hc0; linear_combination M 0 j * ha0 + M 1 j * ha1 - hb j
    have hrel := Fintype.linearIndependent_iff.mp hrows
      (Sum.elim (fun i => a (Sum.inl i)) (fun j => -a (Sum.inr j))) (by
        ext j
        simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three, Sum.elim_inl,
          Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Subfield.smul_def]
        fin_cases j
        · simp [Matrix.row]; linear_combination key 0
        · simp [Matrix.row]; linear_combination key 1
        · simp [Matrix.row]; linear_combination key 2)
    exact hs ⟨by rw [← ha0, show a (Sum.inl 0) = 0 from hrel (Sum.inl 0)]; simp,
      by rw [← ha1, show a (Sum.inl 1) = 0 from hrel (Sum.inl 1)]; simp⟩
  omega
