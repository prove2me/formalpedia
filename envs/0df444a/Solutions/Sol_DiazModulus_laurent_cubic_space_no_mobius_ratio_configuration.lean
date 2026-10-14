-- Prove2me | solution 1 for DiazModulus.laurent_cubic_space_no_mobius_ratio_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:26.738859+00:00
-- url     : https://prove2.me/submissions/1e1eb11c-fd2e-4f44-bb2b-3faf39d2cf24

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The Laurent cubic space carries no Möbius-ratio configuration

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `F = u³/s³ + u²/s²`, `G = ū³/s³ + ū²/s²` and
`W₁ = span_Q̄ {1, u, ū, F, G}`; so `ū u = s²`, `F s³ = u³ + s u²`, `G u³ = s³ + s² u`.

* `{t ∈ W₁ : u t ∈ W₁} ⊆ Q̄ + Q̄ū` (`mem_pair`). For `w = c₁ + c₂u + c₃ū + c₄F + c₅G` the product
  `s³u³ w` is a polynomial of degree `6` in `u` with coefficients `c₅s⁶, c₅s⁵, c₃s⁵, c₁s³, c₂s³,
  c₄s, c₄` (`expand`). Writing `t` and `u t` this way, `u (s³u³ t) = s³u³ (u t)` is a polynomial
  identity of degree `7` over `Q̄` at the transcendental `u`; its coefficients of `u⁷, u⁶, u⁵`
  give `c₄ = 0`, then `c₂ = 0`, and those of `u⁰, u¹` give `c₅ = 0`. So `t = c₁ + c₃ū`.
* Given free `x`, `y` with `x i y j ∈ W₁` and `x₁(γu + δ) = x₀(αu + β)`, `αδ − βγ ≠ 0`, put
  `c = αx₀ − γx₁` and `t_j = c y_j = α x₀y_j − γ x₁y_j ∈ W₁`. The relation gives
  `u t_j = δ x₁y_j − β x₀y_j ∈ W₁`, so `t_j ∈ Q̄ + Q̄ū`. Freeness of `x` gives `c ≠ 0` (else
  `α = γ = 0` and `αδ − βγ = 0`), so the three `t_j` are free, like the `y_j`.
* Three free vectors in the span of two (`linearIndependent_le_span_aux'`): contradiction.
-/

namespace R14_cubicMobius

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

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

/-- Clearing denominators: `σ³u³ w` as a polynomial of degree `6` in `u`. -/
theorem expand {u cu F G w : ℂ} {σ c₁ c₂ c₃ c₄ c₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * σ) = u ^ 3 + σ * u ^ 2)
    (hG : G * u ^ 3 = σ ^ 3 + σ ^ 2 * u) (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * F + c₅ * G) :
    (σ : ℂ) ^ 3 * u ^ 3 * w =
      (c₅ : ℂ) * σ ^ 6 + c₅ * σ ^ 5 * u + c₃ * σ ^ 5 * u ^ 2 + c₁ * σ ^ 3 * u ^ 3 +
      c₂ * σ ^ 3 * u ^ 4 + c₄ * σ * u ^ 5 + c₄ * u ^ 6 := by
  linear_combination (σ : ℂ) ^ 3 * u ^ 3 * h + (c₃ : ℂ) * σ ^ 3 * u ^ 2 * hcu +
    (c₄ : ℂ) * u ^ 3 * hF + (c₅ : ℂ) * σ ^ 3 * hG

/-- `{t ∈ W₁ : u t ∈ W₁} ⊆ Q̄ + Q̄ū`. -/
theorem mem_pair {u cu F G t : ℂ} (hu : u ∉ Qbar) {σ : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * σ) = u ^ 3 + σ * u ^ 2)
    (hG : G * u ^ 3 = σ ^ 3 + σ ^ 2 * u)
    (ht : t ∈ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ))
    (htu : u * t ∈ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ)) :
    t ∈ Submodule.span Qbar ({1, cu} : Set ℂ) := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := coeffs ht
  obtain ⟨d₁, d₂, d₃, d₄, d₅, hd⟩ := coeffs htu
  have EA := expand hcu hF hG hc
  have EB := expand hcu hF hG hd
  obtain ⟨e₀, e₁, -, -, -, e₅, e₆, e₇⟩ := eight_terms hu (a₀ := -(d₅ * σ ^ 6))
    (a₁ := c₅ * σ ^ 6 - d₅ * σ ^ 5) (a₂ := c₅ * σ ^ 5 - d₃ * σ ^ 5)
    (a₃ := c₃ * σ ^ 5 - d₁ * σ ^ 3) (a₄ := c₁ * σ ^ 3 - d₂ * σ ^ 3)
    (a₅ := c₂ * σ ^ 3 - d₄ * σ) (a₆ := c₄ * σ - d₄) (a₇ := c₄)
    (by push_cast; linear_combination EB - u * EA)
  have h2 : c₂ * σ ^ 3 = 0 := by linear_combination e₅ - σ * e₆ + σ ^ 2 * e₇
  have h5 : c₅ * σ ^ 7 = 0 := by linear_combination σ * e₁ - e₀
  have hc₂ := (mul_eq_zero.1 h2).resolve_right (pow_ne_zero 3 hσ)
  have hc₅ := (mul_eq_zero.1 h5).resolve_right (pow_ne_zero 7 hσ)
  refine span_mem_of_eq (show t = c₁ * 1 + c₃ * cu by rw [hc, hc₂, e₇, hc₅]; push_cast; ring)
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

end R14_cubicMobius

open DiazModulus R14_cubicMobius in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (α β γ δ : ℂ), α ∈ Qbar ∧ β ∈ Qbar ∧ γ ∈ Qbar ∧ δ ∈ Qbar ∧
      α * δ - β * γ ≠ 0 ∧ LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧ x 1 * (γ * u + δ) = x 0 * (α * u + β) := by
  rintro ⟨x, y, α, β, γ, δ, hα, hβ, hγ, hδ, hD, hx, hy, hxy, hrel⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hss
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hcu : conj u * u = σ * σ := by rw [hss]; ring
  have hF : (u ^ 3 / (σ * σ * σ) + u ^ 2 / (σ * σ)) * (σ * σ * σ) = u ^ 3 + σ * u ^ 2 := by
    field_simp
  have hG : (conj u ^ 3 / (σ * σ * σ) + conj u ^ 2 / (σ * σ)) * u ^ 3 =
      σ ^ 3 + σ ^ 2 * u := by
    field_simp
    linear_combination ((conj u * u) ^ 2 + conj u * u * σ ^ 2 + σ ^ 4 +
      σ * u * (conj u * u + σ ^ 2)) * hcu
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
  refine no_three hT fun j => mem_pair hu hσ hcu hF hG ?_ ?_
  · exact span_mem_of_eq (show (α * x 0 - γ * x 1) * y j = α * (x 0 * y j) + (-γ) * (x 1 * y j)
      by ring) (Submodule.add_mem _ (span_mul_mem hα (hxy 0 j))
        (span_mul_mem (neg_mem hγ) (hxy 1 j)))
  · exact span_mem_of_eq (show u * ((α * x 0 - γ * x 1) * y j) =
        δ * (x 1 * y j) + (-β) * (x 0 * y j) by linear_combination (-(y j)) * hrel)
      (Submodule.add_mem _ (span_mul_mem hδ (hxy 1 j)) (span_mul_mem (neg_mem hβ) (hxy 0 j)))
