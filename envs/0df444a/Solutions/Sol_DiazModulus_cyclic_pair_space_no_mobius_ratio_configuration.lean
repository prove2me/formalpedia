-- Prove2me | solution 1 for DiazModulus.cyclic_pair_space_no_mobius_ratio_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T11:59:42.896759+00:00
-- url     : https://prove2.me/submissions/6abf9f79-9026-408d-8ca5-1946f61ce72b

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The cyclic pair space carries no Möbius-ratio configuration

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `G₁ = s/(u − s) + 2s/(u + s)`,
`G₂ = s²/(u − s)² + s/(u − s) − 2s²/(u + s)² + 2s/(u + s)` and `W = span_Q̄ {1, u, ū, G₁, G₂}`;
so `ū u = s²`, `G₁ (u² − s²) = s(3u − s)` and `G₂ (u² − s²)² = s u (3u² − 2su + 3s²)`.

* `{t ∈ W : u t ∈ W} ⊆ Q̄ + Q̄ū` (`mem_pair`). For `w = c₁ + c₂u + c₃ū + c₄G₁ + c₅G₂` the product
  `u(u² − s²)² w` is a polynomial of degree `6` in `u` (`expand`). Writing `t` and `u t` this way,
  `u · (u(u² − s²)² t) = u(u² − s²)² (u t)` is a polynomial identity of degree `7` over `Q̄` at the
  transcendental `u`; its `u⁷` coefficient gives `c₂ = 0`, and two combinations of the eight
  coefficient equations give `16 s⁶ c₄ = 0` and `16 s⁶ c₅ = 0`. So `t = c₁ + c₃ū`.
* Given free `x`, `y` with `x i y j ∈ W` and `x₁(γu + δ) = x₀(αu + β)`, `αδ − βγ ≠ 0`, put
  `c = αx₀ − γx₁ ≠ 0` (freeness of `x`) and `t_j = c y_j ∈ W`; then `u t_j = δ x₁y_j − β x₀y_j ∈ W`,
  so the three free `t_j` lie in `Q̄ + Q̄ū`, which is impossible.
-/

namespace R15_cyclicMobius

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem c2 : ((2 : ↥Qbar) : ℂ) = 2 := rfl
theorem c3 : ((3 : ↥Qbar) : ℂ) = 3 := rfl

/-- A polynomial relation of degree `7` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem eight_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 +
      a₆ * u ^ 6 + a₇ * u ^ 7 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 ∧ a₇ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5 + C a₆ * X ^ 6 + C a₇ * X ^ 7)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 7) hP

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- Clearing denominators: `u(u² − σ²)² w` as a polynomial of degree `6` in `u`. -/
theorem expand {u cu G₁ G₂ w : ℂ} {σ c₁ c₂ c₃ c₄ c₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hG₁ : G₁ * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ))
    (hG₂ : G₂ * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2))
    (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * G₁ + c₅ * G₂) :
    u * (u ^ 2 - σ ^ 2) ^ 2 * w =
      (c₃ : ℂ) * σ ^ 6 + (c₁ + c₄) * σ ^ 4 * u +
      ((c₂ - 2 * c₃) * σ ^ 4 + 3 * (c₅ - c₄) * σ ^ 3) * u ^ 2 +
      (-(2 * c₁ + c₄ + 2 * c₅) * σ ^ 2) * u ^ 3 +
      ((c₃ - 2 * c₂) * σ ^ 2 + 3 * (c₄ + c₅) * σ) * u ^ 4 + c₁ * u ^ 5 + c₂ * u ^ 6 := by
  linear_combination u * (u ^ 2 - (σ : ℂ) ^ 2) ^ 2 * h + (c₃ : ℂ) * (u ^ 2 - σ ^ 2) ^ 2 * hcu +
    (c₄ : ℂ) * u * (u ^ 2 - σ ^ 2) * hG₁ + (c₅ : ℂ) * u * hG₂

/-- `{t ∈ W : u t ∈ W} ⊆ Q̄ + Q̄ū`. -/
theorem mem_pair {u cu G₁ G₂ t : ℂ} (hu : u ∉ Qbar) {σ : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : cu * u = σ * σ) (hG₁ : G₁ * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ))
    (hG₂ : G₂ * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2))
    (ht : t ∈ Submodule.span Qbar ({1, u, cu, G₁, G₂} : Set ℂ))
    (htu : u * t ∈ Submodule.span Qbar ({1, u, cu, G₁, G₂} : Set ℂ)) :
    t ∈ Submodule.span Qbar ({1, cu} : Set ℂ) := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := coeffs ht
  obtain ⟨d₁, d₂, d₃, d₄, d₅, hd⟩ := coeffs htu
  have EA := expand hcu hG₁ hG₂ hc
  have EB := expand hcu hG₁ hG₂ hd
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := eight_terms hu (a₀ := -(d₃ * σ ^ 6))
    (a₁ := c₃ * σ ^ 6 - (d₁ + d₄) * σ ^ 4)
    (a₂ := (c₁ + c₄) * σ ^ 4 - ((d₂ - 2 * d₃) * σ ^ 4 + 3 * (d₅ - d₄) * σ ^ 3))
    (a₃ := (c₂ - 2 * c₃) * σ ^ 4 + 3 * (c₅ - c₄) * σ ^ 3 + (2 * d₁ + d₄ + 2 * d₅) * σ ^ 2)
    (a₄ := -(2 * c₁ + c₄ + 2 * c₅) * σ ^ 2 - ((d₃ - 2 * d₂) * σ ^ 2 + 3 * (d₄ + d₅) * σ))
    (a₅ := (c₃ - 2 * c₂) * σ ^ 2 + 3 * (c₄ + c₅) * σ - d₁) (a₆ := c₁ - d₂) (a₇ := c₂)
    (by push_cast [c2, c3]; linear_combination EB - u * EA)
  have h4 : 16 * σ ^ 6 * c₄ = 0 := by
    linear_combination -4 * e₀ - 9 * σ * e₁ - 2 * σ ^ 2 * e₂ - 3 * σ ^ 3 * e₃ +
      3 * σ ^ 5 * e₅ + 2 * σ ^ 6 * e₆ + 9 * σ ^ 7 * e₇
  have h5 : 16 * σ ^ 6 * c₅ = 0 := by
    linear_combination e₀ + 3 * σ * e₁ + σ ^ 2 * e₂ + 3 * σ ^ 3 * e₃ + σ ^ 4 * e₄ +
      3 * σ ^ 5 * e₅ + σ ^ 6 * e₆ + 3 * σ ^ 7 * e₇
  have hn : (16 : ↥Qbar) * σ ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 6 hσ)
  have hc₄ := (mul_eq_zero.1 h4).resolve_left hn
  have hc₅ := (mul_eq_zero.1 h5).resolve_left hn
  refine span_mem_of_eq (show t = c₁ * 1 + c₃ * cu by rw [hc, e₇, hc₄, hc₅]; push_cast; ring)
    (Submodule.add_mem _ (span_mul_mem c₁.2 (Submodule.subset_span (by simp)))
      (span_mul_mem c₃.2 (Submodule.subset_span (by simp))))

/-- Three free vectors do not fit in the span of two. -/
theorem no_three {cu : ℂ} {T : Fin 3 → ℂ} (hT : LinearIndependent (↥Qbar) T)
    (hmem : ∀ j, T j ∈ Submodule.span Qbar ({1, cu} : Set ℂ)) : False := by
  classical
  have h := linearIndependent_le_span_aux' T hT ((({1, cu} : Finset ℂ)) : Set ℂ) (by
    rintro _ ⟨j, rfl⟩
    simpa using hmem j)
  simp only [Fintype.card_fin, Finset.coe_sort_coe, Fintype.card_coe] at h
  exact absurd (h.trans Finset.card_le_two) (by norm_num)

end R15_cyclicMobius

open DiazModulus R15_cyclicMobius in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (α β γ δ : ℂ), α ∈ Qbar ∧ β ∈ Qbar ∧ γ ∈ Qbar ∧ δ ∈ Qbar ∧
      α * δ - β * γ ≠ 0 ∧ LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧ x 1 * (γ * u + δ) = x 0 * (α * u + β) := by
  rintro ⟨x, y, α, β, γ, δ, hα, hβ, hγ, hδ, hD, hx, hy, hxy, hrel⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hss
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hm : u - σ ≠ 0 := sub_ne_zero.2 fun e => hu (by rw [e]; exact σ.2)
  have hp : u + σ ≠ 0 := fun e => hu (by rw [eq_neg_of_add_eq_zero_left e]; exact neg_mem σ.2)
  have hcu : conj u * u = σ * σ := by rw [hss]; ring
  have hG₁ : ((σ : ℂ) / (u - σ) + 2 * σ / (u + σ)) * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ) := by
    field_simp
    ring
  have hG₂ : ((σ : ℂ) * σ / (u - σ) ^ 2 + σ / (u - σ) - 2 * (σ * σ) / (u + σ) ^ 2 +
      2 * σ / (u + σ)) * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2) := by
    field_simp
    ring
  -- `c = αx₀ − γx₁` is non-zero
  have hc : α * x 0 - γ * x 1 ≠ 0 := by
    intro h0
    have hx' := Fintype.linearIndependent_iff.1 hx ![⟨α, hα⟩, ⟨-γ, neg_mem hγ⟩] (by
      simp only [Fin.sum_univ_two, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linear_combination h0)
    have h0' := congrArg Subtype.val (hx' 0)
    have h1' := congrArg Subtype.val (hx' 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ZeroMemClass.coe_zero,
      neg_eq_zero] at h0' h1'
    exact hD (by rw [h0', h1']; ring)
  -- the three numbers `c y_j`
  have hT : LinearIndependent (↥Qbar) (fun j => (α * x 0 - γ * x 1) * y j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    refine Fintype.linearIndependent_iff.1 hy g ?_
    simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul] at hg ⊢
    have : (α * x 0 - γ * x 1) * ((g 0 : ℂ) * y 0 + g 1 * y 1 + g 2 * y 2) = 0 := by
      linear_combination hg
    exact (mul_eq_zero.1 this).resolve_left hc
  refine no_three hT fun j => mem_pair hu hσ hcu hG₁ hG₂ ?_ ?_
  · exact span_mem_of_eq (show (α * x 0 - γ * x 1) * y j = α * (x 0 * y j) + (-γ) * (x 1 * y j)
      by ring) (Submodule.add_mem _ (span_mul_mem hα (hxy 0 j))
        (span_mul_mem (neg_mem hγ) (hxy 1 j)))
  · exact span_mem_of_eq (show u * ((α * x 0 - γ * x 1) * y j) =
        δ * (x 1 * y j) + (-β) * (x 0 * y j) by linear_combination (-(y j)) * hrel)
      (Submodule.add_mem _ (span_mul_mem hδ (hxy 1 j)) (span_mul_mem (neg_mem hβ) (hxy 0 j)))
