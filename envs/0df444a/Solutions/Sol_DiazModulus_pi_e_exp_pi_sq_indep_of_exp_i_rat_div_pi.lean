-- Prove2me | solution 1 for DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T06:50:35.685974+00:00
-- url     : https://prove2.me/submissions/4dd183ea-2a15-4650-9832-10410c6cd7fd

import Mathlib
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_DiazModulus_pi_sq_transcendental
import Theorems.Thm_DiazModulus_pi_transcendental

/-!
# Two of `π`, `e`, `e^{π²}` are algebraically independent when `e^{ir/π}` is algebraic

Let `r ≠ 0` be rational with `e^{ir/π}` algebraic. Apply Waldschmidt's theorem (1973) to

  `x₁ = iπ`, `x₂ = ir/π`, `y₁ = -iπ/r`, `y₂ = 1`.

The `xᵢ` are `ℚ`-linearly independent: `s iπ + t ir/π = 0` gives `s π² + t r = 0`, so `s = 0`
because `π²` is transcendental, and then `t = 0`. The `yⱼ` are `ℚ`-linearly independent because
`y₁` is not real. Moreover `e^{x₁y₂} = e^{iπ} = -1` and `e^{x₂y₂} = e^{ir/π}` are algebraic. So two
of the eight numbers

  `iπ`, `ir/π`, `-iπ/r`, `1`, `e^{x₁y₁} = e^{π²/r}`, `e^{x₁y₂} = -1`, `e^{x₂y₁} = e`,
  `e^{x₂y₂} = e^{ir/π}`

are algebraically independent over `ℚ`.

Suppose that no two of `π`, `e`, `e^{π²}` are algebraically independent. Since `π` is
transcendental, `e` and `e^{π²}` are then algebraic over `ℚ[π]`. So are all eight numbers above:
`i` and the rationals are algebraic, `π` and `1/π` are algebraic over `ℚ[π]`, and writing
`r = n/d`, `(e^{π²/r})^n = (e^{π²})^d`. Hence the `ℚ`-algebra they generate has transcendence
degree at most `1`, which contradicts the two algebraically independent numbers it contains.
-/

namespace R1_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi

/-! ## Numbers algebraic over `ℚ[x]` -/

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def algOver (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_algOver_iff {x z : ℂ} :
    z ∈ algOver x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_algOver_of_isAlgebraic {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ algOver x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem ratCast_mem_algOver (x : ℂ) (q : ℚ) : (q : ℂ) ∈ algOver x :=
  mem_algOver_of_isAlgebraic (isAlgebraic_ratCast ℚ q)

/-- `i` is algebraic over `ℚ`, being a root of `X² + 1`. -/
theorem isAlgebraic_I : IsAlgebraic ℚ Complex.I := by
  refine IsAlgebraic.of_pow (n := 2) two_pos ?_
  rw [Complex.I_sq]
  exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

theorem I_mem_algOver (x : ℂ) : Complex.I ∈ algOver x :=
  mem_algOver_of_isAlgebraic isAlgebraic_I

theorem self_mem_algOver (x : ℂ) : x ∈ algOver x := by
  rw [mem_algOver_iff]
  have h : x = algebraMap ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ ⟨x, Algebra.subset_adjoin rfl⟩ :=
    rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem inv_mem_algOver {x z : ℂ} (h : z ∈ algOver x) : z⁻¹ ∈ algOver x :=
  IsAlgebraic.inv h

theorem mem_algOver_of_pow {x z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n ∈ algOver x) :
    z ∈ algOver x :=
  IsAlgebraic.of_pow hn h

theorem mem_algOver_of_zpow {x z : ℂ} {n : ℤ} (hn : n ≠ 0) (h : z ^ n ∈ algOver x) :
    z ∈ algOver x := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.2 hn
  rcases Int.natAbs_eq n with h' | h'
  · rw [h', zpow_natCast] at h
    exact mem_algOver_of_pow hpos h
  · rw [h', zpow_neg, zpow_natCast] at h
    have h'' := inv_mem_algOver h
    rw [inv_inv] at h''
    exact mem_algOver_of_pow hpos h''

/-! ## Algebraic independence of a pair, and transcendence degree -/

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
theorem mem_algOver_of_not_indep {a b : ℂ} (ha : Transcendental ℚ a)
    (h : ¬ AlgebraicIndependent ℚ ![a, b]) : b ∈ algOver a := by
  by_contra hb
  exact h (algIndep_pair ha fun hb' => hb (mem_algOver_iff.2 hb'))

/-- If every element of `S` is algebraic over `ℚ[x]`, no two elements of `S` are algebraically
independent over `ℚ`. -/
theorem not_algIndep_of_forall_mem_algOver {x : ℂ} {S : Set ℂ} (hS : ∀ s ∈ S, s ∈ algOver x)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) : ¬ AlgebraicIndependent ℚ ![a, b] := by
  intro hab
  have htr := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin (K := ℚ) x S hS
  have hv : AlgebraicIndependent ℚ
      (![⟨a, Algebra.subset_adjoin ha⟩, ⟨b, Algebra.subset_adjoin hb⟩] :
        Fin 2 → ↥(Algebra.adjoin ℚ S)) := by
    apply AlgebraicIndependent.of_comp (Algebra.adjoin ℚ S).val
    convert hab using 1
    funext i
    fin_cases i <;> rfl
  have h2 := hv.cardinalMk_le_trdeg
  rw [Cardinal.mk_fin] at h2
  have h21 := h2.trans htr
  norm_num at h21

/-! ## The choice of `x₁, x₂, y₁, y₂` -/

theorem pi_ne_zero : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 Real.pi_ne_zero

/-- `iπ` and `ir/π` are `ℚ`-linearly independent, because `π²` is irrational. -/
theorem linIndep_x (r : ℚ) (hr : r ≠ 0) :
    LinearIndependent ℚ ![Complex.I * ((Real.pi : ℝ) : ℂ),
      Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def] at hst
  have hπ := pi_ne_zero
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have key : (s : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 + (t : ℂ) * r = 0 := by
    have h' : (s : ℂ) * (Complex.I * ((Real.pi : ℝ) : ℂ)) +
        (t : ℂ) * (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)) =
        Complex.I / ((Real.pi : ℝ) : ℂ) *
          ((s : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 + (t : ℂ) * r) := by
      field_simp
    rw [h'] at hst
    exact (mul_eq_zero.1 hst).resolve_left (div_ne_zero Complex.I_ne_zero hπ)
  have hs : s = 0 := by
    by_contra hs
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    apply DiazModulus.pi_sq_transcendental
    have h' : ((Real.pi ^ 2 : ℝ) : ℂ) = ((-(t * r) / s : ℚ) : ℂ) := by
      push_cast
      field_simp
      linear_combination key
    rw [h']
    exact isAlgebraic_ratCast ℚ _
  subst hs
  refine ⟨rfl, ?_⟩
  simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at key
  rcases key with h | h
  · exact_mod_cast h
  · exact absurd h hrC

/-- `-iπ/r` and `1` are `ℚ`-linearly independent, because `-iπ/r` is not real. -/
theorem linIndep_y (r : ℚ) (hr : r ≠ 0) :
    LinearIndependent ℚ ![-(Complex.I * ((Real.pi : ℝ) : ℂ) / (r : ℂ)), 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def] at hst
  have him := congrArg Complex.im hst
  simp [Real.pi_ne_zero, hr] at him
  subst him
  refine ⟨rfl, ?_⟩
  simpa using hst

end R1_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi

open R1_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi in
theorem solution
    (hW73 : ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b])
    (r : ℚ) (hr : r ≠ 0)
    (halg : IsAlgebraic ℚ (Complex.exp (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)))) :
    ∃ a ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
      ∃ b ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
        AlgebraicIndependent ℚ ![a, b] := by
  by_contra hne
  have hπ : Transcendental ℚ ((Real.pi : ℝ) : ℂ) := DiazModulus.pi_transcendental
  -- `e` and `e^{π²}` are algebraic over `ℚ[π]`
  have he : Complex.exp 1 ∈ algOver ((Real.pi : ℝ) : ℂ) :=
    mem_algOver_of_not_indep hπ fun h => hne ⟨_, by simp, _, by simp, h⟩
  have heπ : Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2) ∈ algOver ((Real.pi : ℝ) : ℂ) :=
    mem_algOver_of_not_indep hπ fun h => hne ⟨_, by simp, _, by simp, h⟩
  have hπ0 := pi_ne_zero
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  -- the hypotheses of Waldschmidt's theorem
  have hx1y2 : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) * 1) = -1 := by
    rw [mul_one, mul_comm]
    exact Complex.exp_pi_mul_I
  have halg12 : IsAlgebraic ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) * 1)) := by
    rw [hx1y2]
    exact isAlgebraic_one.neg
  have halg22 :
      IsAlgebraic ℚ (Complex.exp (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ) * 1)) := by
    rw [mul_one]
    exact halg
  obtain ⟨a, ha, b, hb, hab⟩ := hW73 (Complex.I * ((Real.pi : ℝ) : ℂ))
    (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)) (-(Complex.I * ((Real.pi : ℝ) : ℂ) / (r : ℂ))) 1
    (linIndep_x r hr) (linIndep_y r hr) halg12 halg22
  -- all eight numbers are algebraic over `ℚ[π]`
  refine not_algIndep_of_forall_mem_algOver (x := ((Real.pi : ℝ) : ℂ)) ?_ ha hb hab
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `x₁ = iπ`
    exact mul_mem (I_mem_algOver _) (self_mem_algOver _)
  · -- `x₂ = ir/π`
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (I_mem_algOver _) (ratCast_mem_algOver _ r))
      (inv_mem_algOver (self_mem_algOver _))
  · -- `y₁ = -iπ/r`
    rw [div_eq_mul_inv]
    exact neg_mem (mul_mem (mul_mem (I_mem_algOver _) (self_mem_algOver _))
      (inv_mem_algOver (ratCast_mem_algOver _ r)))
  · -- `y₂ = 1`
    exact one_mem _
  · -- `e^{x₁y₁} = e^{π²/r}`, whose `n`-th power is `(e^{π²})^d` for `r = n/d`
    apply mem_algOver_of_zpow (Rat.num_ne_zero.2 hr)
    have hpow : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) *
        -(Complex.I * ((Real.pi : ℝ) : ℂ) / (r : ℂ))) ^ r.num =
        Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2) ^ r.den := by
      rw [← Complex.exp_int_mul, ← Complex.exp_nat_mul]
      congr 1
      have hnum : (r.num : ℂ) = (r.den : ℂ) * r := by
        exact_mod_cast (Rat.den_mul_eq_num r).symm
      rw [hnum]
      linear_combination (-(r.den : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 * ((r : ℂ) * (r : ℂ)⁻¹)) *
          Complex.I_sq + ((r.den : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) * mul_inv_cancel₀ hrC
    rw [hpow]
    exact pow_mem heπ _
  · -- `e^{x₁y₂} = -1`
    rw [hx1y2]
    exact neg_mem (one_mem _)
  · -- `e^{x₂y₁} = e`
    have h : Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ) *
        -(Complex.I * ((Real.pi : ℝ) : ℂ) / (r : ℂ)) = 1 := by
      field_simp
      linear_combination -Complex.I_sq
    rw [h]
    exact he
  · -- `e^{x₂y₂} = e^{ir/π}`
    exact mem_algOver_of_isAlgebraic halg22
