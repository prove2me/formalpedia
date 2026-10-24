-- Prove2me | solution 1 for DiazModulus.laurent_polynomial_class_conj_hull_two_orbit_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:56:01.977122+00:00
-- url     : https://prove2.me/submissions/95457c97-8dc6-424e-8278-a68ebe8443dc

import Mathlib
import Definitions.Def_DiazModulus

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Complex ComplexConjugate

/-! # The polynomial class is a two-orbit (D2a) span with pencil `(X², 1)`

Let `W = span(1, u, ū, Z, Z̄)` and `w = αu² + βu³ ∈ W` with `(α, β) ≠ 0`. From `s² = uū` we get
`ū = s²/u`, hence `w̄ = (β̄s⁶ + ᾱs⁴u)/u³`. Take `P′ = X²`, `Q′ = 1` (coprime, `max deg = 2`),
`S₁ = β̄s⁶ + ᾱs⁴X`, `S₂ = αX + βX²`; then `Q′S₁/(uP′) = w̄` and `P′S₂/(uQ′) = w`.
(1) `span(1, u, u⁻¹, w̄, w) ≤ W`: `u⁻¹ = ū/s²`; `w ∈ W` by hypothesis; and `W` is conjugation-stable
(its generators are permuted by conjugation, and `Q̄` is conjugation-stable), so `w̄ ∈ W`.
(2) `1, u, u⁻¹, w̄, w` are free over `Q̄`: multiplying a relation by `u³` gives a polynomial in `u` of
degree `≤ 6` with coefficients `x₃β̄s⁶, x₃ᾱs⁴, x₂, x₀, x₁, x₄α, x₄β`; `u` is transcendental over `Q̄`,
so all vanish, and `(α, β) ≠ 0`, `s ≠ 0` give `x₃ = x₄ = 0`.
(3) `W` is spanned by five vectors, so `finrank W ≤ 5 = finrank span(1, u, u⁻¹, w̄, w)`, and (1) is
an equality. No dimension hypothesis on `W` is needed.
-/

namespace R21a_B1

open DiazModulus Polynomial

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- `1, u, …, u⁶` are free over `Q̄` at a transcendental `u`. -/
theorem coeff7 {u : ℂ} (hu : u ∉ Qbar) {c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℂ}
    (h₀ : c₀ ∈ Qbar) (h₁ : c₁ ∈ Qbar) (h₂ : c₂ ∈ Qbar) (h₃ : c₃ ∈ Qbar) (h₄ : c₄ ∈ Qbar)
    (h₅ : c₅ ∈ Qbar) (h₆ : c₆ ∈ Qbar)
    (h : c₀ + c₁ * u + c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5 + c₆ * u ^ 6 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 ∧ c₆ = 0 := by
  lift c₀ to Qbar using h₀; lift c₁ to Qbar using h₁; lift c₂ to Qbar using h₂
  lift c₃ to Qbar using h₃; lift c₄ to Qbar using h₄; lift c₅ to Qbar using h₅
  lift c₆ to Qbar using h₆
  have hP := aeval_eq_zero hu (P := C c₀ + C c₁ * X + C c₂ * X ^ 2 + C c₃ * X ^ 3 +
    C c₄ * X ^ 4 + C c₅ * X ^ 5 + C c₆ * X ^ 6)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; linear_combination h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP

theorem span_mul_mem {S : Set ℂ} {c w : ℂ} (hc : c ∈ Qbar) (hw : w ∈ Submodule.span Qbar S) :
    c * w ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hw
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

/-- The hull `span(1, u, ū, Z, Z̄)` is conjugation-stable. -/
theorem hull_conj {u Z w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, conj u, Z, conj Z} : Set ℂ)) :
    conj w ∈ Submodule.span Qbar ({1, u, conj u, Z, conj Z} : Set ℂ) := by
  refine span_conj_stable (fun x hx => ?_) w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [map_one]; exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · rw [conj_conj]; exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · rw [conj_conj]; exact Submodule.subset_span (by simp)

/-- A five-generator span lies in a submodule containing the five generators. -/
theorem span5_le {a b c d e : ℂ} {W : Submodule (↥Qbar) ℂ} (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hd : d ∈ W) (he : e ∈ W) :
    Submodule.span Qbar ({a, b, c, d, e} : Set ℂ) ≤ W := by
  rw [Submodule.span_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem range5 (a b c d e : ℂ) : Set.range ![a, b, c, d, e] = ({a, b, c, d, e} : Set ℂ) := by
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

/-- The five vectors `1, u, u⁻¹, w̄, w` are free over `Q̄`. -/
theorem li5 {u s α β : ℂ} (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hs0 : s ≠ 0) (hα : α ∈ Qbar)
    (hβ : β ∈ Qbar) (hαβ : α ≠ 0 ∨ β ≠ 0) :
    LinearIndependent (↥Qbar) ![1, u, u⁻¹, 1 * (conj β * s ^ 6 + conj α * s ^ 4 * u) / (u * u ^ 2),
      u ^ 2 * (α * u + β * u ^ 2) / (u * 1)] := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (zero_mem _)
  have hcα := conj_mem hα
  have hcβ := conj_mem hβ
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : (g 0 : ℂ) * 1 + g 1 * u + g 2 * u⁻¹ +
      g 3 * (1 * (conj β * s ^ 6 + conj α * s ^ 4 * u) / (u * u ^ 2)) +
      g 4 * (u ^ 2 * (α * u + β * u ^ 2) / (u * 1)) = 0 := by
    simpa [Fin.sum_univ_five, Subfield.smul_def] using hg
  have hpoly : (g 3 : ℂ) * conj β * s ^ 6 + g 3 * conj α * s ^ 4 * u + g 2 * u ^ 2 + g 0 * u ^ 3 +
      g 1 * u ^ 4 + g 4 * α * u ^ 5 + g 4 * β * u ^ 6 = 0 := by
    have e : u ^ 3 * ((g 0 : ℂ) * 1 + g 1 * u + g 2 * u⁻¹ +
        g 3 * (1 * (conj β * s ^ 6 + conj α * s ^ 4 * u) / (u * u ^ 2)) +
        g 4 * (u ^ 2 * (α * u + β * u ^ 2) / (u * 1))) =
        (g 3 : ℂ) * conj β * s ^ 6 + g 3 * conj α * s ^ 4 * u + g 2 * u ^ 2 + g 0 * u ^ 3 +
          g 1 * u ^ 4 + g 4 * α * u ^ 5 + g 4 * β * u ^ 6 := by
      field_simp <;> ring
    rw [← e, hg', mul_zero]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := coeff7 hu
    (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply pow_mem | apply mul_mem))
    (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply pow_mem | apply mul_mem))
    (SetLike.coe_mem _) (SetLike.coe_mem _) (SetLike.coe_mem _)
    (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply pow_mem | apply mul_mem))
    (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply pow_mem | apply mul_mem))
    hpoly
  have hs4 : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
  have hs6 : s ^ 6 ≠ 0 := pow_ne_zero 6 hs0
  have g3 : (g 3 : ℂ) = 0 := by
    rcases hαβ with hα0 | hβ0
    · have : conj α ≠ 0 := (_root_.map_ne_zero _).2 hα0
      simpa [this, hs4] using h1
    · have : conj β ≠ 0 := (_root_.map_ne_zero _).2 hβ0
      simpa [this, hs6] using h0
  have g4 : (g 4 : ℂ) = 0 := by
    rcases hαβ with hα0 | hβ0
    · simpa [hα0] using h5
    · simpa [hβ0] using h6
  intro i
  fin_cases i
  · exact Subtype.ext h3
  · exact Subtype.ext h4
  · exact Subtype.ext h2
  · exact Subtype.ext g3
  · exact Subtype.ext g4

end R21a_B1

open DiazModulus R21a_B1 in
open Polynomial in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ)
    (α β : ℂ) (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hP : α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) :
    ∃ P' Q' S₁ S₂ : (↥Qbar)[X], aeval u P' = u ^ 2 ∧ aeval u Q' = 1 ∧
      aeval u S₁ = conj β * s ^ 6 + conj α * s ^ 4 * u ∧ aeval u S₂ = α * u + β * u ^ 2 ∧
      IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧ S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
      Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ) := by
  set Z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j with hZ
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : u * conj u = 0 := by rw [← hss]; ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact hu0 h
    · exact hu0 (by simpa using h)
  have hcu : conj u = s * s / u := by field_simp; linear_combination -hss
  set s' : ↥Qbar := ⟨s, hs⟩
  set a' : ↥Qbar := ⟨α, hα⟩
  set b' : ↥Qbar := ⟨β, hβ⟩
  set ca : ↥Qbar := ⟨conj α, conj_mem hα⟩
  set cb : ↥Qbar := ⟨conj β, conj_mem hβ⟩
  have hP' : aeval u (X ^ 2 : (↥Qbar)[X]) = u ^ 2 := by simp
  have hQ' : aeval u (1 : (↥Qbar)[X]) = 1 := map_one _
  have hS1 : aeval u (C (cb * s' ^ 6) + C (ca * s' ^ 4) * X) =
      conj β * s ^ 6 + conj α * s ^ 4 * u := by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rfl
  have hS2 : aeval u (C a' * X + C b' * X ^ 2) = α * u + β * u ^ 2 := by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rfl
  refine ⟨_, _, _, _, hP', hQ', hS1, hS2, isCoprime_one_right, by simp,
    by compute_degree!, by compute_degree!, ?_⟩
  rw [hP', hQ', hS1, hS2]
  -- (1) the explicit span lies in the hull
  have hle : Submodule.span Qbar ({1, u, u⁻¹, 1 * (conj β * s ^ 6 + conj α * s ^ 4 * u) / (u * u ^ 2),
      u ^ 2 * (α * u + β * u ^ 2) / (u * 1)} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, Z, conj Z} : Set ℂ) := by
    apply span5_le
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · have e : u⁻¹ = 1 / (s * s) * conj u := by rw [hcu]; field_simp
      rw [e]
      exact span_mul_mem (div_mem (one_mem _) (mul_mem hs hs)) (Submodule.subset_span (by simp))
    · have e : 1 * (conj β * s ^ 6 + conj α * s ^ 4 * u) / (u * u ^ 2) =
          conj (α * u ^ 2 + β * u ^ 3) := by
        simp only [map_add, map_mul, map_pow, hcu]; field_simp <;> ring
      rw [e]
      exact hull_conj hP
    · have e : u ^ 2 * (α * u + β * u ^ 2) / (u * 1) = α * u ^ 2 + β * u ^ 3 := by
        field_simp <;> ring
      rw [e]
      exact hP
  -- (2) the explicit span has dimension five, (3) the hull at most five
  have hR5 := finrank_span_eq_card (li5 hu hs hs0 hα hβ hαβ)
  rw [range5, Fintype.card_fin] at hR5
  have hW5 := finrank_range_le_card (R := ↥Qbar) ![1, u, conj u, Z, conj Z]
  rw [range5, Fintype.card_fin] at hW5
  have : FiniteDimensional (↥Qbar) (Submodule.span Qbar ({1, u, conj u, Z, conj Z} : Set ℂ)) :=
    FiniteDimensional.span_of_finite _ (Set.toFinite _)
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hR5]; exact hW5)).symm
