-- Prove2me | solution 1 for DiazModulus.log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T18:06:34.256452+00:00
-- url     : https://prove2.me/submissions/9edec8e3-d79a-4109-88d9-9b6403c4db03

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin

namespace P17_prop1

/-!
# Diaz 1997, Proposition 1

If `l₁, l₂` are logarithms of algebraic numbers, `l₁` is not a rational multiple of `2πi`, and
`l₁ l₂ = c π²` with `c ∈ ℚ ∖ {0}`, then both `{l₁, l₂}` and `{l₁, 2πi}` are algebraically
independent over `ℚ`.

Write `T := 2πi`. If either pair were dependent, then `T` and `l₂` would both be algebraic over
`ℚ[l₁]` (using `T² = -4π² = -4 l₁ l₂ / c`), and four exponentials in transcendence degree one,
applied to `[[l₁, (-c/4) T], [T, l₂]]`, would force `l₁ ∈ ℚ T`.
-/

/-! ## Numbers algebraic over `ℚ[x]` -/

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {x z : ℂ} : z ∈ E x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem rat_mem_E (x : ℂ) (q : ℚ) : (q : ℂ) ∈ E x :=
  mem_E_of_alg (isAlgebraic_algebraMap q)

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

/-! ## Algebraic independence of a pair -/

/-- A pair `![a, b]` is algebraically independent over `ℚ` as soon as `a` is transcendental
over `ℚ` and `b` is transcendental over `ℚ[a]`. -/
theorem algIndep_pair {a b : ℂ} (ha : Transcendental ℚ a)
    (hb : Transcendental ↥(Algebra.adjoin ℚ ({a} : Set ℂ)) b) :
    AlgebraicIndependent ℚ ![a, b] := by
  have hind : AlgebraicIndependent ℚ (fun _ : Unit => a) :=
    (algebraicIndependent_singleton_iff ()).2 ha
  have htrans : Transcendental ↥(Algebra.adjoin ℚ (Set.range fun _ : Unit => a)) b := by
    rw [Set.range_const]
    exact hb
  have hopt := (hind.option_iff_transcendental b).2 htrans
  have he : Function.Injective (![some (), none] : Fin 2 → Option Unit) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  convert hopt.comp _ he using 1
  funext i
  fin_cases i <;> rfl

/-- If `a` is transcendental and `![a, b]` is algebraically dependent, then `b` is algebraic
over `ℚ[a]`. -/
theorem mem_E_of_not_indep {a b : ℂ} (ha : Transcendental ℚ a)
    (h : ¬ AlgebraicIndependent ℚ ![a, b]) : b ∈ E a := by
  by_contra hb
  exact h (algIndep_pair ha (fun hb' => hb (mem_E_iff.2 hb')))

/-! ## Facts about `T = 2πi` -/

theorem T_ne_zero : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
  Complex.two_pi_I_ne_zero

theorem exp_T : Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) = 1 :=
  Complex.exp_two_pi_mul_I

theorem T_sq :
    (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 = -4 * ((Real.pi : ℝ) : ℂ) ^ 2 := by
  linear_combination (4 * ((Real.pi : ℝ) : ℂ) ^ 2) * Complex.I_sq

theorem pi_sq_ne_zero : ((Real.pi : ℝ) : ℂ) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)

/-- `exp (q · 2πi)` is a root of unity, hence algebraic. -/
theorem exp_rat_mul_T_alg (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  have hden : (q.den : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    exact_mod_cast congrArg (fun r : ℚ => (r : ℂ)) (Rat.den_mul_eq_num q)
  have key : (Complex.exp ((q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul, ← mul_assoc (q.den : ℂ) (q : ℂ), hden]
    exact Complex.exp_eq_one_iff.2 ⟨q.num, rfl⟩
  have hpow : IsAlgebraic ℚ
      ((Complex.exp ((q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))) ^ q.den) := by
    rw [key]
    exact isAlgebraic_one
  exact IsAlgebraic.of_pow q.pos hpow

/-- Hermite–Lindemann in the form used here: a non-zero logarithm of an algebraic number is
transcendental. -/
theorem transc_of_exp {z : ℂ} (hz : z ≠ 0) (he : IsAlgebraic ℚ (Complex.exp z)) :
    Transcendental ℚ z := fun h => DiazModulus.hermite_lindemann_holds z hz h he

/-! ## The linear relations -/

/-- A non-trivial rational relation `a l + b T = 0` with `T ≠ 0` makes `l` a rational multiple
of `T`. -/
theorem no_rel {l T : ℂ} (hT0 : T ≠ 0) (hroot : ∀ q : ℚ, l ≠ (q : ℂ) * T) (a b : ℚ)
    (hab : ¬(a = 0 ∧ b = 0)) (h : (a : ℂ) * l + (b : ℂ) * T = 0) : False := by
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := fun hb => hab ⟨rfl, hb⟩
    simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at h
    rcases h with h | h
    · exact hb (by exact_mod_cast h)
    · exact hT0 h
  · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    apply hroot (-b / a)
    push_cast
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff haC]
    linear_combination -h

/-! ## The key lemma -/

/-- If both `T = 2πi` and `l₂` are algebraic over `ℚ[l₁]`, four exponentials in transcendence
degree one on `[[l₁, (-c/4) T], [T, l₂]]` gives a contradiction. -/
theorem key (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hroot : ∀ q : ℚ, l₁ ≠ (q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
    (c : ℚ) (hc : c ≠ 0) (hprod : l₁ * l₂ = (c : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2)
    (hT : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ∈ E l₁) (hl₂ : l₂ ∈ E l₁) : False := by
  have hT0 := T_ne_zero
  have hl₁0 : l₁ ≠ 0 := by simpa using hroot 0
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hl₂0 : l₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact mul_ne_zero hcC pi_sq_ne_zero hprod.symm
  have hq : (-c / 4 : ℚ) ≠ 0 := by
    intro h
    apply hc
    linarith
  have h12 : ((-c / 4 : ℚ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hq) hT0
  have hdet : l₁ * l₂ = (((-c / 4 : ℚ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) *
      (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [hprod, mul_assoc, ← sq, T_sq]
    push_cast
    ring
  have htr := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin (K := ℚ) l₁
    ({l₁, ((-c / 4 : ℚ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I),
      2 * ((Real.pi : ℝ) : ℂ) * Complex.I, l₂} : Set ℂ) (by
      intro s hs
      rw [← mem_E_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with h | h | h | h <;> rw [h]
      · exact self_mem_E l₁
      · exact mul_mem (rat_mem_E _ _) hT
      · exact hT
      · exact hl₂)
  have hexpT : IsAlgebraic ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) := by
    rw [exp_T]
    exact isAlgebraic_one
  rcases DiazModulus.four_exponentials_trdeg_one l₁
      (((-c / 4 : ℚ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
      (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) l₂ h₁ (exp_rat_mul_T_alg _) hexpT h₂
      hl₁0 h12 hT0 hl₂0 hdet htr with ⟨a, b, hab, h1, -⟩ | ⟨a, b, hab, h1, -⟩
  · -- rows: `a l₁ + b T = 0`
    exact no_rel hT0 hroot a b hab h1
  · -- columns: `a l₁ + b (-c/4) T = 0`
    refine no_rel hT0 hroot a (b * (-c / 4)) ?_ ?_
    · rintro ⟨ha, hb⟩
      apply hab
      refine ⟨ha, ?_⟩
      rcases mul_eq_zero.1 hb with hb | hb
      · exact hb
      · exact absurd hb hq
    · push_cast at h1 ⊢
      linear_combination h1

end P17_prop1

open P17_prop1 in
theorem solution (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hroot : ∀ q : ℚ, l₁ ≠ (q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
    (c : ℚ) (hc : c ≠ 0) (hprod : l₁ * l₂ = (c : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) :
    AlgebraicIndependent ℚ ![l₁, l₂] ∧
      AlgebraicIndependent ℚ ![l₁, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] := by
  have hl₁0 : l₁ ≠ 0 := by simpa using hroot 0
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have htr₁ : Transcendental ℚ l₁ := transc_of_exp hl₁0 h₁
  constructor
  · -- if `![l₁, l₂]` is dependent, `l₂` and then `T` are algebraic over `ℚ[l₁]`
    by_contra hdep
    have hl₂ : l₂ ∈ E l₁ := mem_E_of_not_indep htr₁ hdep
    have hT : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ∈ E l₁ := by
      apply mem_E_of_sq
      have hsq : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 =
          ((-4 / c : ℚ) : ℂ) * (l₁ * l₂) := by
        rw [hprod, T_sq]
        push_cast
        rw [div_mul_eq_mul_div, eq_div_iff hcC]
        ring
      rw [hsq]
      exact mul_mem (rat_mem_E _ _) (mul_mem (self_mem_E l₁) hl₂)
    exact key l₁ l₂ h₁ h₂ hroot c hc hprod hT hl₂
  · -- if `![l₁, T]` is dependent, `T` and then `l₂` are algebraic over `ℚ[l₁]`
    by_contra hdep
    have hT : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ∈ E l₁ := mem_E_of_not_indep htr₁ hdep
    have hl₂ : l₂ ∈ E l₁ := by
      apply mem_E_of_mul hl₁0 (self_mem_E l₁)
      have hmul : l₁ * l₂ =
          ((-c / 4 : ℚ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 := by
        rw [hprod, T_sq]
        push_cast
        ring
      rw [hmul]
      exact mul_mem (rat_mem_E _ _) (pow_mem hT 2)
    exact key l₁ l₂ h₁ h₂ hroot c hc hprod hT hl₂

#print axioms solution
