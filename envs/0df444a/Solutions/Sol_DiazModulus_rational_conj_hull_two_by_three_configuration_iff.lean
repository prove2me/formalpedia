-- Prove2me | solution 1 for DiazModulus.rational_conj_hull_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:21:51.915561+00:00
-- url     : https://prove2.me/submissions/030f340a-737e-4430-bf90-a9068648d670

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rational_space_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_rational_conj_hull_le_adjoin
import Theorems.Thm_DiazModulus_conj_hull_finrank_four_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_circle_point_config_card_le_four

open Complex ComplexConjugate

/-! # Theorem F: configurations in `W_z = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` for `z ∈ Q̄(u)`

`W_z` is spanned by five vectors, so `dim W_z ≤ 5`, and it contains `H = span(1, u, ū)`, which has
dimension `3`: from `a + b u + c ū = 0`, multiplying by `u` gives `c ρ + a u + b u² = 0` with
`ρ = u ū ∈ Q̄` non-zero, and `u` is transcendental over `Q̄`. So `dim W_z ∈ {3, 4, 5}`.
* `dim W_z = 3`: then `W_z = H`, and a `2 × 3` configuration in `H` contradicts
  `circle_point_config_card_le_four` (with `K = Q̄`, `p + q ≤ 4`).
* `dim W_z = 4`: this is `conj_hull_finrank_four_two_by_three_configuration_iff` (Theorem B).
* `dim W_z = 5`: `rational_conj_hull_le_adjoin` gives `u⁻¹ ∈ W_z` and `W_z ⊆ Q̄(u)`, so
  `rational_space_two_by_three_configuration_iff` applies to `W = W_z` and gives D1, D2a or D2b.
Both directions of the equivalence follow from these three cases.
-/

namespace R20_C20

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_eq (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

theorem quad_zero {z : ℂ} (hz : Transcendental (↥Qbar) z) (a₀ a₁ a₂ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * z + a₂ * z ^ 2 = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have hP := transcendental_iff.1 hz (C a₀ + C a₁ * X + C a₂ * X ^ 2) (by simpa [am] using h)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hP
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP

/-- `1, u, ū` are free over `Q̄` when `u ∉ Q̄` and `u ū ∈ Q̄`. -/
theorem free3 {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, smul_eq, mul_one] at hg
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hρ0 : (⟨u * conj u, mem_Qbar_iff.2 hρ⟩ : ↥Qbar) ≠ 0 := by
    intro h
    have h' : u * conj u = 0 := congrArg Subtype.val h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact hu0 h''
    · exact hu0 (by simpa using h'')
  have e : ((g 2 * ⟨u * conj u, mem_Qbar_iff.2 hρ⟩ : ↥Qbar) : ℂ) = g 2 * (u * conj u) := rfl
  obtain ⟨h0, h1, h2⟩ := quad_zero (tr_of_not_mem hu) (g 2 * ⟨u * conj u, mem_Qbar_iff.2 hρ⟩)
    (g 0) (g 1) (by rw [e]; linear_combination u * hg)
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact (mul_eq_zero.1 h0).resolve_right hρ0

theorem range3 (a b c : ℂ) : Set.range ![a, b, c] = ({a, b, c} : Set ℂ) := by
  ext w
  simp [Matrix.range_cons, Matrix.range_empty]
  tauto

end R20_C20

open DiazModulus R20_C20 Polynomial in
theorem solution (u z : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (hz : z ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔
      (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4 ∧ ∃ a ∈ Qbar, a * conj a = u * conj u ∧
          z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) ∨
      (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 5 ∧
        ((∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
        (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)))) := by
  obtain ⟨hui, hrat⟩ := DiazModulus.rational_conj_hull_le_adjoin u z hu hρ hz
  have h4iff := DiazModulus.conj_hull_finrank_four_two_by_three_configuration_iff u z hu hρ
  set Wz := Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) with hWz
  have : FiniteDimensional (↥Qbar) Wz := FiniteDimensional.span_of_finite _ (Set.toFinite _)
  have hmemW : ∀ w ∈ ({1, u, conj u, z, conj z} : Set ℂ), w ∈ Wz :=
    fun w hw => Submodule.subset_span hw
  have h1 : (1 : ℂ) ∈ Wz := hmemW _ (by simp)
  have hu1 : u ∈ Wz := hmemW _ (by simp)
  have h5iff := fun h5 => DiazModulus.rational_space_two_by_three_configuration_iff u hu Wz h5 h1
    hu1 hui hrat
  have hle5 : Module.finrank (↥Qbar) Wz ≤ 5 := by
    have h := (finrank_span_finset_le_card (R := ↥Qbar)
      ({1, u, conj u, z, conj z} : Finset ℂ)).trans Finset.card_le_five
    have e : ((({1, u, conj u, z, conj z} : Finset ℂ)) : Set ℂ) = {1, u, conj u, z, conj z} := by
      simp
    rw [e] at h
    exact h
  constructor
  · intro hconf
    by_cases h4 : Module.finrank (↥Qbar) Wz = 4
    · exact Or.inl ⟨h4, (h4iff h4).1 hconf⟩
    by_cases h5 : Module.finrank (↥Qbar) Wz = 5
    · exact Or.inr ⟨h5, (h5iff h5).1 hconf⟩
    exfalso
    obtain ⟨x, y, hx, hy, hxy⟩ := hconf
    have hH3 : Module.finrank (↥Qbar) (Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, conj u])) = 3 := by
      rw [finrank_span_eq_card (free3 hu hρ)]
      simp
    have hHle : Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, conj u]) ≤ Wz :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => by
        fin_cases i <;> exact hmemW _ (by simp))
    have hHW := Submodule.eq_of_le_of_finrank_le hHle (by omega)
    have hxy' : ∀ i j, x i * y j ∈ Submodule.span (↥Qbar) ({1, u, conj u} : Set ℂ) := by
      intro i j
      have h := hxy i j
      rw [← hHW, range3] at h
      exact h
    have := DiazModulus.circle_point_config_card_le_four Qbar u (tr_of_not_mem hu)
      (mem_Qbar_iff.2 hρ) 2 3 (by norm_num) (by norm_num) x y hx hy hxy'
    omega
  · rintro (⟨h4, h⟩ | ⟨h5, h⟩)
    · exact (h4iff h4).2 h
    · exact (h5iff h5).2 h
