-- Prove2me | solution 1 for DiazModulus.generic_period_never_enters
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T05:05:41.917657+00:00
-- url     : https://prove2.me/submissions/9164cebf-ef88-4e43-8596-fadebd889ee7

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one_field
import Theorems.Thm_DiazModulus_generic_quadratic_relation_is_norm

open Complex ComplexConjugate

namespace P14Period

/-- Polarisation of a quadratic identity on `Fin 4 → ℂ`. -/
theorem polar (P : Fin 4 → Fin 4 → ℂ) (c ρ : ℂ)
    (hQ : ∀ x : Fin 4 → ℂ, ∑ k, ∑ l, P k l * x k * x l = c * (x 1 * x 2 - ρ * x 0 ^ 2))
    (x y : Fin 4 → ℂ) :
    ∑ k, ∑ l, (P k l + P l k) * x k * y l = c * (x 1 * y 2 + x 2 * y 1 - 2 * ρ * x 0 * y 0) := by
  have h1 := hQ (x + y)
  have h2 := hQ x
  have h3 := hQ y
  simp only [Fin.sum_univ_four, Pi.add_apply] at h1 h2 h3 ⊢
  linear_combination h1 - h2 - h3

/-- The polar form evaluated on two basis vectors. -/
theorem polar_single (P : Fin 4 → Fin 4 → ℂ) (c ρ : ℂ)
    (hQ : ∀ x : Fin 4 → ℂ, ∑ k, ∑ l, P k l * x k * x l = c * (x 1 * x 2 - ρ * x 0 ^ 2))
    (k l : Fin 4) :
    P k l + P l k = c * ((Pi.single k 1 : Fin 4 → ℂ) 1 * (Pi.single l 1 : Fin 4 → ℂ) 2
      + (Pi.single k 1 : Fin 4 → ℂ) 2 * (Pi.single l 1 : Fin 4 → ℂ) 1
      - 2 * ρ * (Pi.single k 1 : Fin 4 → ℂ) 0 * (Pi.single l 1 : Fin 4 → ℂ) 0) := by
  have h := polar P c ρ hQ (Pi.single k 1) (Pi.single l 1)
  rw [← h]
  simp [Pi.single_apply]

end P14Period

open P14Period in
/-- Write `C k` for the `2 × 2` matrix `(C i j k)` and `B(X, Y) = X₀₀Y₁₁ + X₁₁Y₀₀ - X₀₁Y₁₀ - X₁₀Y₀₁`
(twice the polar form of `det`), so that `B(C k, C l) = P k l + P l k`.
(i) `det M = 0` is a quadratic relation among `1, u, conj u, πi`; by N6 it is
`c · (x₁x₂ - ρx₀²)` with `c` algebraic.
(ii) If `c = 0`, all `B(C k, C l)` vanish; N5 over `Q̄` gives an algebraic row or column relation,
which `hrow` / `hcol` forbid. So `c ≠ 0`.
(iii) Polarising gives `B(C 3, C k) = 0` for every `k` and the Gram matrix `[[-2cρ,0,0],[0,0,c],[0,c,0]]`
of `C 0, C 1, C 2`. Let `V` be the coordinate matrix of `C 0, …, C 3` and `y` the `B`-dual of `C 3`,
so `y ᵥ* V = 0`. If `y ≠ 0` then `det V = 0`, and a kernel vector `w` of `V` pairs with `C 0, C 1, C 2`
to give `w 0 = w 1 = w 2 = 0`, hence `w 3 ≠ 0` and `C 3 = 0`. If `y = 0`, then `C 3 = 0` directly. -/
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (C : Fin 2 → Fin 2 → Fin 4 → ℂ) (hC : ∀ i j k, IsAlgebraic ℚ (C i j k))
    (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = C i j 0 + C i j 1 * u + C i j 2 * conj u + C i j 3 * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0)
    (hrow : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      (∀ j, p * M 0 j + q * M 1 j = 0) → p = 0 ∧ q = 0)
    (hcol : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      (∀ i, p * M i 0 + q * M i 1 = 0) → p = 0 ∧ q = 0) :
    ∀ i j, C i j 3 = 0 := by
  -- (i) the determinant relation is a quadratic relation among `1, u, conj u, πi`
  set P : Fin 4 → Fin 4 → ℂ := fun k l => C 0 0 k * C 1 1 l - C 0 1 k * C 1 0 l with hPdef
  have hPalg : ∀ k l, IsAlgebraic ℚ (P k l) := fun k l =>
    ((hC 0 0 k).mul (hC 1 1 l)).sub ((hC 0 1 k).mul (hC 1 0 l))
  have hrel : ∑ k, ∑ l, P k l * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k
      * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] l = 0 := by
    simp only [Fin.sum_univ_four, hPdef]
    simp
    rw [hM 0 0, hM 1 1, hM 0 1, hM 1 0] at hdet
    linear_combination hdet
  obtain ⟨c, hc_alg, hQ⟩ :=
    DiazModulus.generic_quadratic_relation_is_norm u hu hρ hgen P hPalg hrel
  set ρ : ℂ := u * conj u with hρdef
  have hρ0 : ρ ≠ 0 := mul_ne_zero hu (by simpa using hu)
  -- (ii) `c ≠ 0`
  have hc0 : c ≠ 0 := by
    intro hc
    have hB0 : ∀ k l, C 0 0 k * C 1 1 l + C 0 0 l * C 1 1 k
        = C 0 1 k * C 1 0 l + C 0 1 l * C 1 0 k := by
      intro k l
      have h := polar_single P c ρ hQ k l
      rw [hc, zero_mul] at h
      simp only [hPdef] at h
      linear_combination h
    let A : Fin 2 → Fin 2 → Fin 4 → ↥DiazModulus.Qbar :=
      fun i j k => ⟨C i j k, DiazModulus.mem_Qbar_iff.2 (hC i j k)⟩
    have hA : ∀ i j k, ((A i j k : ↥DiazModulus.Qbar) : ℂ) = C i j k := fun _ _ _ => rfl
    have hdetA : ∀ k l : Fin 4,
        A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
      intro k l
      apply Subtype.ext
      simp only [Subfield.coe_add, Subfield.coe_mul, hA]
      exact hB0 k l
    rcases DiazModulus.det_zero_linear_forms_rank_one_field 4 A hdetA with
      ⟨p, q, hpq, hr⟩ | ⟨p, q, hpq, hr⟩
    · have hr' : ∀ j k, (p : ℂ) * C 0 j k + (q : ℂ) * C 1 j k = 0 := by
        intro j k
        have := congrArg Subtype.val (hr j k)
        simpa [hA] using this
      have hM' : ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0 := by
        intro j
        rw [hM 0 j, hM 1 j]
        linear_combination hr' j 0 + u * hr' j 1 + conj u * hr' j 2
          + (((Real.pi : ℝ) : ℂ) * Complex.I) * hr' j 3
      obtain ⟨hp, hq⟩ := hrow p q (DiazModulus.mem_Qbar_iff.1 p.2)
        (DiazModulus.mem_Qbar_iff.1 q.2) hM'
      exact hpq ⟨Subtype.ext hp, Subtype.ext hq⟩
    · have hr' : ∀ i k, (p : ℂ) * C i 0 k + (q : ℂ) * C i 1 k = 0 := by
        intro i k
        have := congrArg Subtype.val (hr i k)
        simpa [hA] using this
      have hM' : ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0 := by
        intro i
        rw [hM i 0, hM i 1]
        linear_combination hr' i 0 + u * hr' i 1 + conj u * hr' i 2
          + (((Real.pi : ℝ) : ℂ) * Complex.I) * hr' i 3
      obtain ⟨hp, hq⟩ := hcol p q (DiazModulus.mem_Qbar_iff.1 p.2)
        (DiazModulus.mem_Qbar_iff.1 q.2) hM'
      exact hpq ⟨Subtype.ext hp, Subtype.ext hq⟩
  -- (iii) the values of the polar form `B(C k, C l) = P k l + P l k`
  have hb := polar_single P c ρ hQ
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h02 := hb 0 2
  have h03 := hb 0 3
  have h11 := hb 1 1
  have h12 := hb 1 2
  have h13 := hb 1 3
  have h22 := hb 2 2
  have h23 := hb 2 3
  have h33 := hb 3 3
  simp only [hPdef, Pi.single_apply, Fin.reduceEq, if_true, if_false, mul_one, mul_zero, add_zero,
    sub_zero] at h00 h01 h02 h03 h11 h12 h13 h22 h23 h33
  -- coordinates of `C 0, …, C 3`, and the `B`-dual `y` of `C 3`: `(y ᵥ* V) k = B(C k, C 3) = 0`
  let V : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r k => ![C 0 0 k, C 0 1 k, C 1 0 k, C 1 1 k] r
  let y : Fin 4 → ℂ := ![C 1 1 3, -C 1 0 3, -C 0 1 3, C 0 0 3]
  have hyV : Matrix.vecMul y V = 0 := by
    funext k
    fin_cases k <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, V, y]
    · linear_combination h03
    · linear_combination h13
    · linear_combination h23
    · linear_combination h33
  have key : C 0 0 3 = 0 ∧ C 0 1 3 = 0 ∧ C 1 0 3 = 0 ∧ C 1 1 3 = 0 := by
    by_cases hy : y = 0
    · have e0 := congrFun hy 0
      have e1 := congrFun hy 1
      have e2 := congrFun hy 2
      have e3 := congrFun hy 3
      simp [y] at e0 e1 e2 e3
      exact ⟨e3, e2, e1, e0⟩
    · have hV : V.det = 0 := Matrix.exists_vecMul_eq_zero_iff.mp ⟨y, hy, hyV⟩
      obtain ⟨w, hw, hVw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hV
      -- `Σ w k • C k = 0`; pairing it with `C 0`, `C 2`, `C 1` through `B` kills `w 0`, `w 1`, `w 2`
      have Ea := congrFun hVw 0
      have Eb := congrFun hVw 1
      have Ec := congrFun hVw 2
      have Ed := congrFun hVw 3
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, V] at Ea Eb Ec Ed
      have hw0 : w 0 = 0 := by
        have h : (-2 * c * ρ) * w 0 = 0 := by
          linear_combination C 1 1 0 * Ea + C 0 0 0 * Ed - C 1 0 0 * Eb - C 0 1 0 * Ec
            - w 0 * h00 - w 1 * h01 - w 2 * h02 - w 3 * h03
        have hne : (-2 * c * ρ) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hc0) hρ0
        exact (mul_eq_zero.1 h).resolve_left hne
      have hw2 : w 2 = 0 := by
        have h : c * w 2 = 0 := by
          linear_combination C 1 1 1 * Ea + C 0 0 1 * Ed - C 1 0 1 * Eb - C 0 1 1 * Ec
            - w 0 * h01 - w 1 * h11 - w 2 * h12 - w 3 * h13
        exact (mul_eq_zero.1 h).resolve_left hc0
      have hw1 : w 1 = 0 := by
        have h : c * w 1 = 0 := by
          linear_combination C 1 1 2 * Ea + C 0 0 2 * Ed - C 1 0 2 * Eb - C 0 1 2 * Ec
            - w 0 * h02 - w 1 * h12 - w 2 * h22 - w 3 * h23
        exact (mul_eq_zero.1 h).resolve_left hc0
      have hw3 : w 3 ≠ 0 := by
        intro h3
        apply hw
        funext r
        fin_cases r <;> simp [hw0, hw1, hw2, h3]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h : C 0 0 3 * w 3 = 0 := by
          linear_combination Ea - C 0 0 0 * hw0 - C 0 0 1 * hw1 - C 0 0 2 * hw2
        exact (mul_eq_zero.1 h).resolve_right hw3
      · have h : C 0 1 3 * w 3 = 0 := by
          linear_combination Eb - C 0 1 0 * hw0 - C 0 1 1 * hw1 - C 0 1 2 * hw2
        exact (mul_eq_zero.1 h).resolve_right hw3
      · have h : C 1 0 3 * w 3 = 0 := by
          linear_combination Ec - C 1 0 0 * hw0 - C 1 0 1 * hw1 - C 1 0 2 * hw2
        exact (mul_eq_zero.1 h).resolve_right hw3
      · have h : C 1 1 3 * w 3 = 0 := by
          linear_combination Ed - C 1 1 0 * hw0 - C 1 1 1 * hw1 - C 1 1 2 * hw2
        exact (mul_eq_zero.1 h).resolve_right hw3
  intro i j
  fin_cases i <;> fin_cases j
  exacts [key.1, key.2.1, key.2.2.1, key.2.2.2]

#print axioms solution
