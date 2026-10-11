-- Prove2me | solution 1 for DiazModulus.involution_pencil_space_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:28:16.769982+00:00
-- url     : https://prove2.me/submissions/69d260a1-ac81-4b98-b1ae-5c26fa17a5f6

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The involution-pencil space carries a two-by-three configuration

Let `u ∉ Q̄`, `q₁, q₂ ∈ Q̄[X]` coprime of degree at most `2`, one of them of degree exactly `2`,
and `l₁, l₂` non-zero members of the pencil `Q̄q₁ + Q̄q₂`. Write `A = q₁(u)`, `B = q₂(u)`,
`D = u l₁(u) l₂(u)`, and let `W` be the `Q̄`-span of `1, u, u⁻¹` and of `AⁱB³⁻ⁱ/D`, `i = 0..3`.
Put `r = A/B`, `c = B³/D`, `x = (1, r)`, `y = (c, cr, cr²)`. The products `xᵢyⱼ = c r^(i+j)` are
`c rᵏ = AᵏB³⁻ᵏ/D`, `k = 0..3`, which are spanning elements of `W`.

Non-vanishing: `u` is transcendental over `Q̄`, so a non-zero polynomial over `Q̄` does not
vanish at `u`; `q₂ ≠ 0` since otherwise `q₁` would be a unit (coprime with `0`) and neither
polynomial would have degree `2`; so `B, l₁(u), l₂(u), u` and `c` are non-zero.
Freeness: `r ∉ Q̄`, since `r ∈ Q̄` gives `q₁ = r q₂` (the polynomial `q₁ - r q₂` vanishes at `u`),
so `q₂` is coprime with itself, a unit, and both degrees are `0`. Hence `r` is transcendental
over `Q̄` too, and `a + b r + e r² = 0` forces `a = b = e = 0`; this gives the freeness of
`x` and, after cancelling `c ≠ 0`, of `y`.
-/

namespace R9_pencilConfig

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem algebraMap_coe (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- `a + b r + e r² = 0` with `r ∉ Q̄` forces `a = b = e = 0`. -/
theorem three_terms {r : ℂ} (hr : r ∉ Qbar) {a b e : ↥Qbar}
    (h : (a : ℂ) + b * r + e * r ^ 2 = 0) : a = 0 ∧ b = 0 ∧ e = 0 := by
  have hP := aeval_eq_zero hr (P := C a + C b * X + C e * X ^ 2)
    (by simp only [map_add, map_mul, aeval_C, aeval_X, aeval_X_pow, algebraMap_coe]; exact h)
  have h0 := congrArg (coeff · 0) hP
  have h1 := congrArg (coeff · 1) hP
  have h2 := congrArg (coeff · 2) hP
  simp [coeff_C, coeff_X, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- Coprime polynomials of degree at most `2`, one of degree `2`: the second is non-zero. -/
theorem q₂_ne_zero {q₁ q₂ : (↥Qbar)[X]} (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂) : q₂ ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  rcases hdeg with h | h <;> simp_all

/-- The ratio `q₁(u)/q₂(u)` is not algebraic. -/
theorem ratio_not_mem {u : ℂ} (hu : u ∉ Qbar) {q₁ q₂ : (↥Qbar)[X]}
    (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂) (hB : aeval u q₂ ≠ 0) :
    aeval u q₁ / aeval u q₂ ∉ Qbar := by
  intro hr
  have hP := aeval_eq_zero hu (P := q₁ - C ⟨_, hr⟩ * q₂)
    (by simp only [map_sub, map_mul, aeval_C, algebraMap_coe]; field_simp; ring)
  rw [sub_eq_zero] at hP
  rw [hP] at hcop
  have hu₂ := isCoprime_self.1 hcop.of_mul_left_right
  have h₂ := natDegree_eq_zero_of_isUnit hu₂
  have h₁ : q₁.natDegree = 0 := by
    rw [hP]; refine Nat.le_zero.1 (natDegree_mul_le.trans ?_); simp [h₂]
  omega

end R9_pencilConfig

open DiazModulus R9_pencilConfig Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  have hu0 := ne_zero_of_not_mem hu
  have hB : aeval u q₂ ≠ 0 := fun h => q₂_ne_zero hdeg hcop (aeval_eq_zero hu h)
  have hL₁ : aeval u l₁ ≠ 0 := fun h => hl₁0 (aeval_eq_zero hu h)
  have hL₂ : aeval u l₂ ≠ 0 := fun h => hl₂0 (aeval_eq_zero hu h)
  have hr := ratio_not_mem hu hdeg hcop hB
  set A := aeval u q₁ with hA
  set B := aeval u q₂ with hBdef
  set D := u * aeval u l₁ * aeval u l₂ with hD
  have hD0 : D ≠ 0 := mul_ne_zero (mul_ne_zero hu0 hL₁) hL₂
  set r := A / B with hrdef
  set c := B ^ 3 / D with hc
  have hc0 : c ≠ 0 := div_ne_zero (pow_ne_zero 3 hB) hD0
  set S : Set ℂ := ({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
    A ^ (i : ℕ) * B ^ (3 - (i : ℕ)) / D) with hS
  have key : ∀ n : ℕ, (hn : n < 4) → c * r ^ n ∈ Submodule.span Qbar S := by
    intro n hn
    refine span_mem_of_eq ?_ (Submodule.subset_span (Or.inr ⟨⟨n, hn⟩, rfl⟩))
    simp only [hc, hrdef, div_pow]
    rw [← pow_sub_mul_pow B (show n ≤ 3 by omega)]
    field_simp
  refine ⟨![1, r], ![c, c * r, c * r ^ 2], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (s : ℂ) + t * r + (0 : ↥Qbar) * r ^ 2 = 0 := by
      simpa [Subfield.smul_def] using h
    obtain ⟨e0, e1, -⟩ := three_terms hr h'
    exact ⟨e0, e1⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : c * ((g 0 : ℂ) + g 1 * r + g 2 * r ^ 2) = 0 := by
      simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul] at hg
      linear_combination hg
    obtain ⟨e0, e1, e2⟩ := three_terms hr ((mul_eq_zero.1 hg').resolve_left hc0)
    intro i
    fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j
    · exact span_mem_of_eq (show (1 : ℂ) * c = c * r ^ 0 by ring) (key 0 (by norm_num))
    · exact span_mem_of_eq (show (1 : ℂ) * (c * r) = c * r ^ 1 by ring) (key 1 (by norm_num))
    · exact span_mem_of_eq (show (1 : ℂ) * (c * r ^ 2) = c * r ^ 2 by ring) (key 2 (by norm_num))
    · exact span_mem_of_eq (show r * c = c * r ^ 1 by ring) (key 1 (by norm_num))
    · exact span_mem_of_eq (show r * (c * r) = c * r ^ 2 by ring) (key 2 (by norm_num))
    · exact span_mem_of_eq (show r * (c * r ^ 2) = c * r ^ 3 by ring) (key 3 (by norm_num))
