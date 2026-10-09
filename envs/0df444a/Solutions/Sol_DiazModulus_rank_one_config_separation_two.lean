-- Prove2me | solution 1 for DiazModulus.rank_one_config_separation_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:53:10.160982+00:00
-- url     : https://prove2.me/submissions/eca41422-b54d-4825-9a71-d7546b8b0a31

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Separation for a 2 × 2 configuration and one transcendental number
Write `x i * y j = c i j + ℓ i j * w` with `c i j ∈ V₀ ⊆ F` and `ℓ i j ∈ K`
(`Submodule.mem_sup`, `Submodule.mem_span_singleton`). Since `(x₀y₀)(x₁y₁) = (x₀y₁)(x₁y₀)`, the
polynomial `det (C + X L)` over `F` vanishes at `w`; as `w` is transcendental over `F`, its leading
coefficient `det L` is `0`. Suppose a column `j` of `L` is non-zero and put
`z = ℓ₁ⱼ x₀ − ℓ₀ⱼ x₁`, non-zero because `x` is `K`-independent. As `det L = 0`, `z yₖ = dₖ ∈ F` for
both `k`. For each row `i`, `(z y₀)(xᵢ y₁) = (z y₁)(xᵢ y₀)` is linear in `w` with coefficients in
`F`, so `d₀ ℓᵢ₁ = d₁ ℓᵢ₀`, i.e. `z (ℓᵢ₁ y₀ − ℓᵢ₀ y₁) = 0`; `K`-independence of `y` gives
`ℓᵢ₀ = ℓᵢ₁ = 0` for every `i`, against the choice of `j`. Hence `L = 0` and `xᵢ yⱼ = cᵢⱼ ∈ V₀`.
-/

namespace R6_sep22
open DiazModulus

/-- `a + b w + d w² = 0` with `a, b, d ∈ F` and `w` transcendental over `F` forces `a = b = d = 0`. -/
theorem quad_eq_zero (F : Subfield ℂ) (w : ℂ) (hw : Transcendental F w) (a b d : F)
    (h : (a : ℂ) + b * w + d * w ^ 2 = 0) : a = 0 ∧ b = 0 ∧ d = 0 := by
  open Polynomial in
  have hP : aeval w (C a + C b * X + C d * X ^ 2 : F[X]) = 0 := by
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow]; exact h
  have h0 : (C a + C b * X + C d * X ^ 2 : F[X]) = 0 := by
    by_contra hne
    exact hw ⟨_, hne, hP⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (Polynomial.coeff · 0) h0
  · simpa using congrArg (Polynomial.coeff · 1) h0
  · simpa using congrArg (Polynomial.coeff · 2) h0

/-- A `K`-relation `a v₀ + b v₁ = 0` between independent `v₀, v₁` is trivial. -/
theorem pair_zero (K : Subfield ℂ) (v : Fin 2 → ℂ) (hv : LinearIndependent K v) (a b : K)
    (h : (a : ℂ) * v 0 + b * v 1 = 0) : a = 0 ∧ b = 0 := by
  have := Fintype.linearIndependent_iff.mp hv ![a, b]
    (by simpa [Fin.sum_univ_two, Subfield.smul_def] using h)
  exact ⟨this 0, this 1⟩

end R6_sep22

open DiazModulus R6_sep22 in
theorem solution (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (w : ℂ) (hw : Transcendental F w)
    (x y : Fin 2 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K {w}) :
    ∀ i j, x i * y j ∈ V₀ := by
  have hdec : ∀ i j, ∃ c ∈ V₀, ∃ l : K, x i * y j = c + l * w := by
    intro i j
    obtain ⟨c, hc, z, hz, he⟩ := Submodule.mem_sup.mp (hxy i j)
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨c, hc, l, by rw [← he, Subfield.smul_def, smul_eq_mul]⟩
  choose c hc ℓ h using hdec
  let cF : Fin 2 → Fin 2 → F := fun i j => ⟨c i j, hV₀ _ (hc i j)⟩
  let lF : Fin 2 → Fin 2 → F := fun i j => ⟨ℓ i j, hKF (ℓ i j).2⟩
  -- `det L = 0`
  obtain ⟨-, -, h2⟩ := quad_eq_zero F w hw
    (cF 0 0 * cF 1 1 - cF 0 1 * cF 1 0)
    (cF 0 0 * lF 1 1 + lF 0 0 * cF 1 1 - cF 0 1 * lF 1 0 - lF 0 1 * cF 1 0)
    (lF 0 0 * lF 1 1 - lF 0 1 * lF 1 0) (by
      simp only [cF, lF, Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_add]
      linear_combination (-(x 1 * y 1)) * h 0 0 - (c 0 0 + ℓ 0 0 * w) * h 1 1
        + (x 1 * y 0) * h 0 1 + (c 0 1 + ℓ 0 1 * w) * h 1 0)
  have hdetL : (ℓ 0 0 : ℂ) * ℓ 1 1 - ℓ 0 1 * ℓ 1 0 = 0 := by
    simpa [lF] using congrArg Subtype.val h2
  have hcross : ∀ j k, (ℓ 1 j : ℂ) * ℓ 0 k - ℓ 0 j * ℓ 1 k = 0 := by
    intro j k
    fin_cases j <;> fin_cases k <;> simp <;>
      first | ring1 | linear_combination hdetL | linear_combination -hdetL
  have hcol : ∀ j, ℓ 0 j = 0 ∧ ℓ 1 j = 0 := by
    intro j
    by_contra hj
    set z : ℂ := ℓ 1 j * x 0 - ℓ 0 j * x 1 with hzdef
    have hz : z ≠ 0 := by
      intro hz0
      have := pair_zero K x hx (ℓ 1 j) (-ℓ 0 j) (by push_cast; linear_combination hz0)
      exact hj ⟨neg_eq_zero.mp this.2, this.1⟩
    let d : Fin 2 → F := fun k => lF 1 j * cF 0 k - lF 0 j * cF 1 k
    have hd : ∀ k, z * y k = d k := by
      intro k
      simp only [d, cF, lF, Subfield.coe_sub, Subfield.coe_mul]
      linear_combination ℓ 1 j * h 0 k - ℓ 0 j * h 1 k + w * hcross j k
    have hrow : ∀ i, ℓ i 0 = 0 ∧ ℓ i 1 = 0 := by
      intro i
      obtain ⟨-, h1, -⟩ := quad_eq_zero F w hw (d 0 * cF i 1 - d 1 * cF i 0)
        (d 0 * lF i 1 - d 1 * lF i 0) 0 (by
          simp only [cF, lF, Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_zero]
          linear_combination -(x i * y 1) * hd 0 - (d 0 : ℂ) * h i 1 + (x i * y 0) * hd 1
            + (d 1 : ℂ) * h i 0)
      have h1' : (d 0 : ℂ) * ℓ i 1 - d 1 * ℓ i 0 = 0 := by
        simpa [lF] using congrArg Subtype.val h1
      have hzy : z * ((ℓ i 1 : ℂ) * y 0 + (-ℓ i 0 : K) * y 1) = 0 := by
        push_cast
        linear_combination (ℓ i 1 : ℂ) * hd 0 - (ℓ i 0 : ℂ) * hd 1 + h1'
      have := pair_zero K y hy (ℓ i 1) (-ℓ i 0) ((mul_eq_zero.mp hzy).resolve_left hz)
      exact ⟨neg_eq_zero.mp this.2, this.1⟩
    have e : ∀ i k, ℓ i k = 0 := fun i k => by
      fin_cases k
      exacts [(hrow i).1, (hrow i).2]
    exact hj ⟨e 0 j, e 1 j⟩
  intro i j
  rw [h i j]
  fin_cases i
  · simpa [(hcol j).1] using hc 0 j
  · simpa [(hcol j).2] using hc 1 j
