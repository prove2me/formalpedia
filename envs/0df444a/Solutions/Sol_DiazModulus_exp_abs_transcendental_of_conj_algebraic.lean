-- Prove2me | solution 1 for DiazModulus.exp_abs_transcendental_of_conj_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T11:05:04.644231+00:00
-- url     : https://prove2.me/submissions/6562aa18-97f4-42ab-8df0-373f9eeb0c9e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace P16_exp_abs_transcendental_of_conj_algebraic

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ DiazModulus.Qbar :=
  DiazModulus.mem_Qbar_iff.symm

theorem isAlg_rat (r : ℚ) : IsAlgebraic ℚ (r : ℂ) :=
  isAlgebraic_algebraMap r

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

/-- Hermite–Lindemann in the form used here: a non-zero logarithm of an algebraic number is
transcendental. -/
theorem transc_of_exp {z : ℂ} (hz : z ≠ 0) (he : IsAlgebraic ℚ (Complex.exp z)) :
    Transcendental ℚ z := fun h => DiazModulus.hermite_lindemann_holds z hz h he

theorem rho_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem pI_ne_zero : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero

theorem exp_pI_alg : IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_pi_mul_I]; simpa using isAlg_rat (-1)

theorem conj_pI :
    conj (((Real.pi : ℝ) : ℂ) * Complex.I) = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

/-- `iπ` is transcendental, by Hermite–Lindemann, since `exp (iπ) = -1`. -/
theorem pI_transc : Transcendental ℚ (((Real.pi : ℝ) : ℂ) * Complex.I) :=
  transc_of_exp pI_ne_zero exp_pI_alg

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`. -/
theorem trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra ℚ ℂ} {x : ℂ} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) y) :
    Algebra.trdeg ℚ ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin ℚ ({x'} : Set ↥B))
      = Algebra.adjoin ℚ ({x} : Set ℂ) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ≃ₐ[ℚ] ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* ℂ)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({x'} : Set ↥B)

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {x z : ℂ} : z ∈ E x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem self_mem_E (x : ℂ) : x ∈ E x := by
  rw [mem_E_iff]
  have h : x = algebraMap ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ
      ⟨x, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem mem_E_of_mul {x a z : ℂ} (ha0 : a ≠ 0) (ha : a ∈ E x) (h : a * z ∈ E x) :
    z ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ha0) (mem_E_iff.1 ha) h

theorem mem_E_of_sq {x z : ℂ} (h : z ^ 2 ∈ E x) : z ∈ E x :=
  (mem_E_iff.1 h).of_pow (by norm_num)

/-- Any `ℚ`-subalgebra of `E x` has transcendence degree at most one. -/
theorem trdeg_le_one_of_le_E {B : Subalgebra ℚ ℂ} {x : ℂ} (h : B ≤ E x) :
    Algebra.trdeg ℚ ↥B ≤ 1 :=
  (trdeg_le_of_injective (Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)).trans
    (trdeg_le_one_of_adjoin_singleton (self_mem_E x) (fun _ hy => hy))

/-- Four exponentials in transcendence degree one on `[[|λ|, λ̄], [λ, |λ|]]`, whose determinant is
`|λ|² - λ λ̄ = 0`, when `λ` and `λ̄` are both algebraic over `ℚ[x]`. -/
theorem core (lam x : ℂ) (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hlE : lam ∈ E x) (hcE : conj lam ∈ E x) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  intro hr
  have hl0 : lam ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have hcl0 : conj lam ≠ 0 := (map_ne_zero _).2 hl0
  have hr0 : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hl0)
  have hrr : ((‖lam‖ : ℝ) : ℂ) * ((‖lam‖ : ℝ) : ℂ) = conj lam * lam := by
    rw [← sq, ← rho_eq, mul_comm]
  have hrE : ((‖lam‖ : ℝ) : ℂ) ∈ E x := by
    apply mem_E_of_sq
    rw [sq, hrr]
    exact mul_mem hcE hlE
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ
      ({((‖lam‖ : ℝ) : ℂ), conj lam, lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)) ≤ 1 := by
    refine trdeg_le_one_of_le_E (x := x) (Algebra.adjoin_le ?_)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h | h <;> rw [h] <;> assumption
  have hreal : ∀ q : ℚ, lam ≠ (q : ℂ) * ((‖lam‖ : ℝ) : ℂ) := by
    intro q h
    apply him
    rw [h]
    simp
  rcases DiazModulus.four_exponentials_trdeg_one _ _ _ _ hr (exp_conj_alg hlam) hlam hr
      hr0 hcl0 hl0 hr0 hrr htr with ⟨a, b, hab, h1, -⟩ | ⟨a, b, hab, -, h2⟩
  · -- rows: `a |λ| + b λ = 0`
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := fun ha => hab ⟨ha, rfl⟩
      simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero] at h1
      rcases h1 with h | h
      · exact ha (by exact_mod_cast h)
      · exact hr0 h
    · have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
      apply hreal (-a / b)
      push_cast
      field_simp
      linear_combination h1
  · -- columns: `a λ + b |λ| = 0`
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := fun hb => hab ⟨rfl, hb⟩
      simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at h2
      rcases h2 with h | h
      · exact hb (by exact_mod_cast h)
      · exact hr0 h
    · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      apply hreal (-b / a)
      push_cast
      field_simp
      linear_combination h2

end P16_exp_abs_transcendental_of_conj_algebraic

open P16_exp_abs_transcendental_of_conj_algebraic in
theorem solution (lam : ℂ)
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({lam} : Set ℂ))) (conj lam)) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  exact core lam lam hlam him (self_mem_E lam) hdep

#print axioms solution
