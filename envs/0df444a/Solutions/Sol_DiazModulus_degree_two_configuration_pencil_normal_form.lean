-- Prove2me | solution 1 for DiazModulus.degree_two_configuration_pencil_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:14.466747+00:00
-- url     : https://prove2.me/submissions/8865a929-f59e-43b4-a137-3b8a806b9997

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_two_configuration_multiplier_complement
import Theorems.Thm_DiazModulus_coprime_pencil_mobius
import Theorems.Thm_DiazModulus_quadratic_complement_eigen_forms

open Complex ComplexConjugate

/-! # Theorem NF with the pencil kept

As in Theorem NF (`degree_two_configuration_normal_form`): `x₀ ≠ 0`, `q(u) ≠ 0`, the triple
`y′ = x₀ y` is free with `y′ ⊆ W` and `(p(u)/q(u)) y′ ⊆ W`, so
`DiazModulus.degree_two_configuration_multiplier_complement` gives `λ` and `g₁, g₂` with
`W = ⟨1, u, u⁻¹, g₁, g₂⟩` and `k gⱼ ∈ W` for `k = q(u)/E`, `E = p(u) − λ q(u)`.
`DiazModulus.quadratic_complement_eigen_forms` for the pencil `(q, p − λq)` gives three cases, all
with denominators `q − c E`, a Möbius image of `(p, q)`:
- scalar and cyclic: `P′ = q − cE = −c p + (1 + cλ) q`, `Q′ = E = p − λ q`, determinant `−1`;
  the shapes are already the target ones;
- two-orbit (`c₁ ≠ c₂`): `P′ = q − c₁E`, `Q′ = q − c₂E`, determinant `c₂ − c₁`. Since
  `P′ − Q′ = (c₂ − c₁) E`, the generators `E R₁/(uP′)`, `E R₂/(uQ′)` differ from
  `Q′S₁/(uP′)`, `P′S₂/(uQ′)` (`S₁ = −R₁/(c₂ − c₁)`, `S₂ = R₂/(c₂ − c₁)`) by `S₁(u)/u`, `S₂(u)/u ∈ H₀`,
  so the two spans agree. -/

namespace R21b_LNF

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

/-- `R(u)/u ∈ H₀` when `deg R ≤ 2`. -/
theorem quad_div_mem {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have e : aeval u R / u = (R.coeff 1 : ℂ) + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
    rw [aeval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
    field_simp
    ring
  have hs : ∀ x ∈ ({1, u, u⁻¹} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (Submodule.smul_mem _ (R.coeff 1) (hs 1 (by simp)))
    (Submodule.smul_mem _ (R.coeff 2) (hs u (by simp))))
    (Submodule.smul_mem _ (R.coeff 0) (hs u⁻¹ (by simp)))
  rw [e]
  simpa only [smul_def', mul_one] using this

/-- Generators that differ by elements of `H₀` span the same space over `H₀`. -/
theorem span_le_of_sub {u A B A' B' : ℂ} (hA : A' - A ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ))
    (hB : B' - B ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) :
    Submodule.span Qbar ({1, u, u⁻¹, A, B} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹, A', B'} : Set ℂ) := by
  have hH : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹, A', B'} : Set ℂ) :=
    Submodule.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hA' : A' ∈ Submodule.span Qbar ({1, u, u⁻¹, A', B'} : Set ℂ) := Submodule.subset_span (by simp)
  have hB' : B' ∈ Submodule.span Qbar ({1, u, u⁻¹, A', B'} : Set ℂ) := Submodule.subset_span (by simp)
  rw [Submodule.span_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact hH (Submodule.subset_span (by simp))
  · exact hH (Submodule.subset_span (by simp))
  · exact hH (Submodule.subset_span (by simp))
  · simpa using sub_mem hA' (hH hA)
  · simpa using sub_mem hB' (hH hB)

/-- The two-orbit generators, `P′ = q − k₁E`, `Q′ = q − k₂E`, differ by `s(u)/u`. -/
theorem key {u r q E k₁ k₂ s : ℂ} (hu : u ≠ 0) (h₁ : q - k₁ * E ≠ 0) (hs : s * (k₂ - k₁) = -r) :
    (q - k₂ * E) * s / (u * (q - k₁ * E)) - E * r / (u * (q - k₁ * E)) = s / u := by
  rw [div_sub_div_same, div_eq_div_iff (mul_ne_zero hu h₁) hu]
  linear_combination (-(u * E)) * hs

/-- The Möbius image `−c p + (1 + cλ) q` of the pencil, at `u`. -/
theorem aeval_pencil (u : ℂ) (p q : (↥Qbar)[X]) (c lam : ↥Qbar) :
    aeval u (C (-c) * p + C (1 + c * lam) * q) = aeval u q - (c : ℂ) * (aeval u p - (lam : ℂ) * aeval u q) := by
  simp only [map_add, map_mul, aeval_C, am]; push_cast; ring

end R21b_LNF

open DiazModulus R21b_LNF in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    ∃ a b c d : ↥Qbar, a * d - b * c ≠ 0 ∧
      ((∀ R : (↥Qbar)[X], R.natDegree ≤ 2 →
          aeval u (C c * p + C d * q) * aeval u R / (u * aeval u (C a * p + C b * q)) ∈ W) ∨
       (∃ S₁ S₂ : (↥Qbar)[X], S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u (C c * p + C d * q) * aeval u S₁ / (u * aeval u (C a * p + C b * q)),
            aeval u (C a * p + C b * q) * aeval u S₂ / (u * aeval u (C c * p + C d * q))} : Set ℂ)) ∨
       (∃ S₁ S₂ : (↥Qbar)[X], S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u (C c * p + C d * q) * aeval u S₁ / (u * aeval u (C a * p + C b * q)),
            aeval u (C c * p + C d * q) * (aeval u (C c * p + C d * q) * aeval u S₁ + aeval u (C a * p + C b * q) * aeval u S₂) /
              (u * aeval u (C a * p + C b * q) ^ 2)} : Set ℂ))) := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hq : aeval u q ≠ 0 := by
    intro hq0
    have hp0 : aeval u p = 0 := by
      have h' := hpq
      rw [hq0, mul_zero] at h'
      exact (mul_eq_zero.mp h'.symm).resolve_left hx0
    obtain ⟨a, b, hab⟩ := id hcop
    have h' := congrArg (aeval u) hab
    simp [hp0, hq0] at h'
  -- the triple `y' = x₀ y`
  have hy' : LinearIndependent (↥Qbar) (fun j => x 0 * y j) :=
    hy.map' (LinearMap.mulLeft (↥Qbar) (x 0)) (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hx0))
  have hyh : ∀ j, aeval u p / aeval u q * (x 0 * y j) ∈ W := fun j => by
    have e : aeval u p / aeval u q * (x 0 * y j) = x 1 * y j := by
      rw [div_mul_eq_mul_div, div_eq_iff hq]
      linear_combination (-(y j)) * hpq
    rw [e]; exact hxy 1 j
  obtain ⟨lam, -, g₁, g₂, hWeq, hg₁, hg₂⟩ :=
    DiazModulus.degree_two_configuration_multiplier_complement u hu W hW h1 hu1 hui p q hcop hdeg
      (fun j => x 0 * y j) hy' (fun j => hxy 0 j) hyh
  -- the pencil `(q, p − λ q)`
  obtain ⟨hcop', hdeg'⟩ := DiazModulus.coprime_pencil_mobius p q hcop hdeg 0 1 1 (-lam) (by simp)
  have hPu : aeval u (C 0 * p + C 1 * q) = aeval u q := by simp
  have hQu : aeval u (C 1 * p + C (-lam) * q) = aeval u p - (lam : ℂ) * aeval u q := by
    simp only [map_add, map_mul, aeval_C, am]; push_cast; ring
  have hS : Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ) = W := by
    rw [hWeq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h5 : Module.finrank (↥Qbar)
      (Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ)) = 5 := by
    rw [hS]; exact hW
  have hk : ∀ j, aeval u (C 0 * p + C 1 * q) / aeval u (C 1 * p + C (-lam) * q) * ![g₁, g₂] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ) := by
    intro j
    rw [hS, hPu, hQu]
    fin_cases j
    · exact hg₁
    · exact hg₂
  have hform := DiazModulus.quadratic_complement_eigen_forms u hu _ _ hcop' hdeg' ![g₁, g₂] h5 hk
  rw [hS, hPu, hQu] at hform
  rcases hform with ⟨c, hc⟩ | ⟨c₁, c₂, hne, R₁, R₂, hR₁, hR₂, hW2⟩ | ⟨c, R₀, R₁, hR₀, hR₁, hW3⟩
  · -- scalar
    refine ⟨-c, 1 + c * lam, 1, -lam, by ring_nf; simp, Or.inl ?_⟩
    rw [hQu, aeval_pencil]
    exact hc
  · -- two-orbit
    have hne' : (c₂ : ℂ) - c₁ ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h).symm
    have hdet : -c₁ * (1 + c₂ * lam) - (1 + c₁ * lam) * -c₂ ≠ 0 := by
      have : -c₁ * (1 + c₂ * lam) - (1 + c₁ * lam) * -c₂ = c₂ - c₁ := by ring
      rw [this]; exact sub_ne_zero.2 fun h => hne h.symm
    obtain ⟨hc', hd'⟩ := DiazModulus.coprime_pencil_mobius p q hcop hdeg _ _ _ _ hdet
    have hPne : aeval u q - (c₁ : ℂ) * (aeval u p - (lam : ℂ) * aeval u q) ≠ 0 := by
      rw [← aeval_pencil u p q c₁ lam]
      exact aeval_ne_zero hu (q_ne_zero hc'.symm (by rw [max_comm]; exact hd'))
    have hQne : aeval u q - (c₂ : ℂ) * (aeval u p - (lam : ℂ) * aeval u q) ≠ 0 := by
      rw [← aeval_pencil u p q c₂ lam]
      exact aeval_ne_zero hu (q_ne_zero hc' hd')
    have hS₁ := (natDegree_C_mul_le (-(1 / (c₂ - c₁))) R₁).trans hR₁
    have hS₂ := (natDegree_C_mul_le (1 / (c₂ - c₁)) R₂).trans hR₂
    have e₁ : aeval u (C (-(1 / (c₂ - c₁))) * R₁) = -(aeval u R₁ / ((c₂ : ℂ) - c₁)) := by
      simp only [map_mul, aeval_C, am]; push_cast; ring
    have e₂ : aeval u (C (1 / (c₂ - c₁)) * R₂) = aeval u R₂ / ((c₂ : ℂ) - c₁) := by
      simp only [map_mul, aeval_C, am]; push_cast; ring
    have m₁ := quad_div_mem hu0 hS₁
    have m₂ := quad_div_mem hu0 hS₂
    rw [e₁] at m₁
    rw [e₂] at m₂
    refine ⟨-c₁, 1 + c₁ * lam, -c₂, 1 + c₂ * lam, hdet, Or.inr (Or.inl ⟨_, _, hS₁, hS₂, ?_⟩)⟩
    rw [aeval_pencil, aeval_pencil, e₁, e₂, hW2]
    generalize aeval u p - (lam : ℂ) * aeval u q = E at hPne hQne ⊢
    have k₁ : -(aeval u R₁ / ((c₂ : ℂ) - c₁)) * ((c₂ : ℂ) - c₁) = -aeval u R₁ := by
      rw [neg_mul, div_mul_cancel₀ _ hne']
    have k₂ : aeval u R₂ / ((c₂ : ℂ) - c₁) * ((c₁ : ℂ) - c₂) = -aeval u R₂ := by
      rw [← neg_sub (c₂ : ℂ), mul_neg, div_mul_cancel₀ _ hne']
    apply le_antisymm
    · apply span_le_of_sub
      · rw [key hu0 hPne k₁]; exact m₁
      · rw [key hu0 hQne k₂]; exact m₂
    · apply span_le_of_sub
      · convert neg_mem m₁ using 1
        linear_combination -(key hu0 hPne k₁)
      · convert neg_mem m₂ using 1
        linear_combination -(key hu0 hQne k₂)
  · -- cyclic
    refine ⟨-c, 1 + c * lam, 1, -lam, by ring_nf; simp, Or.inr (Or.inr ⟨R₀, R₁, hR₀, hR₁, ?_⟩)⟩
    rw [hQu, aeval_pencil]
    exact hW3
