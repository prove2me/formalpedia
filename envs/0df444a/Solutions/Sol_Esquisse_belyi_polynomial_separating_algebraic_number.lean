-- Prove2me | solution 1 for Esquisse.belyi_polynomial_separating_algebraic_number
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:48:22.987128+00:00
-- url     : https://prove2.me/submissions/a3a2b45b-a6de-4a3f-8c34-5487394a9c43

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Definitions.Def_esquisse_dessins_basic
import Theorems.Thm_Esquisse_belyi_theorem_polynomial_form


/-!
UNVERIFIED LOCAL DRAFT. No compiler or publication is claimed.
Source: Lando–Zvonkin, Graphs on Surfaces and Their Applications,
Lemmas 2.4.16–2.4.17, printed pp.125–126.

The substantive step is the noncancellation of the geometric power-difference
factor when the components have the same leading coefficient, in characteristic
zero. Lower outer terms then have insufficient degree to cancel that factor.
-/
namespace DessinsSeparation
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

private lemma geometric_factor_degree (U V : K[X])
    (hU : U ≠ 0) (hV : V ≠ 0)
    (hdeg : U.natDegree = V.natDegree)
    (hlc : U.leadingCoeff = V.leadingCoeff) (m : ℕ) :
    let Q := ∑ i ∈ Finset.range (m + 1), U ^ i * V ^ (m - i)
    Q ≠ 0 ∧ Q.natDegree = m * V.natDegree := by
  classical
  dsimp only
  have hterm (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      (U ^ i * V ^ (m - i)).natDegree = m * V.natDegree := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ hU) (pow_ne_zero _ hV),
      Polynomial.natDegree_pow, Polynomial.natDegree_pow, hdeg, ← add_mul]
    congr 1
    have hi' := Finset.mem_range.mp hi
    omega
  have hc (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      (U ^ i * V ^ (m - i)).coeff (m * V.natDegree) = V.leadingCoeff ^ m := by
    rw [← hterm i hi, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow, hlc, ← pow_add]
    congr 1
    have hi' := Finset.mem_range.mp hi
    omega
  have hsumcoeff :
      (∑ i ∈ Finset.range (m + 1), U ^ i * V ^ (m - i)).coeff (m * V.natDegree) =
        (m + 1 : K) * V.leadingCoeff ^ m := by
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl hc]
    simp [nsmul_eq_mul]
  have hn : (m + 1 : K) * V.leadingCoeff ^ m ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (show m + 1 ≠ 0 by omega)
    · exact pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hV)
  have hcoeff :
      (∑ i ∈ Finset.range (m + 1), U ^ i * V ^ (m - i)).coeff (m * V.natDegree) ≠ 0 := by
    rw [hsumcoeff]
    exact hn
  constructor
  · intro he
    simpa [he] using hcoeff
  · apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hcoeff
    apply Polynomial.natDegree_sum_le_of_forall_le
    exact fun i hi => (hterm i hi).le

private lemma power_difference_degree (U V : K[X])
    (hU : U ≠ 0) (hV : V ≠ 0)
    (hdeg : U.natDegree = V.natDegree)
    (hlc : U.leadingCoeff = V.leadingCoeff)
    (hUV : U - V ≠ 0) (m : ℕ) :
    (U ^ (m + 1) - V ^ (m + 1)).natDegree =
      m * V.natDegree + (U - V).natDegree := by
  have hfactor := geometric_factor_degree U V hU hV hdeg hlc m
  have he : (∑ i ∈ Finset.range (m + 1), U ^ i * V ^ (m - i)) * (U - V) =
      U ^ (m + 1) - V ^ (m + 1) := by
    simpa using geom_sum₂_mul U V (m + 1)
  rw [← he, Polynomial.natDegree_mul hfactor.1 hUV, hfactor.2]

/-- Equality of composites with equal-degree, equal-leading-coefficient right
components forces the right components to differ by a constant. -/
private lemma constant_difference_of_comp_eq (f g U V : K[X])
    (hf : 0 < f.natDegree) (hU : 0 < U.natDegree)
    (hdeg : U.natDegree = V.natDegree)
    (hlc : U.leadingCoeff = V.leadingCoeff)
    (heq : f.comp U = g.comp V) : (U - V).natDegree = 0 := by
  have hV : 0 < V.natDegree := hdeg ▸ hU
  have hU0 : U ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hU
  have hV0 : V ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hV
  have hf0 : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hf
  have houter : f.natDegree = g.natDegree := by
    have hd := congrArg Polynomial.natDegree heq
    simp only [Polynomial.natDegree_comp, hdeg] at hd
    nlinarith
  have houterlc : f.leadingCoeff = g.leadingCoeff := by
    have hc := congrArg Polynomial.leadingCoeff heq
    rw [Polynomial.leadingCoeff_comp (Nat.ne_of_gt hU),
      Polynomial.leadingCoeff_comp (Nat.ne_of_gt hV), hlc, houter] at hc
    exact mul_right_cancel₀ (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hV0)) hc
  by_contra hdiff
  have hk : 0 < (U - V).natDegree := Nat.pos_of_ne_zero hdiff
  have hUV : U - V ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  have hpow : (U ^ f.natDegree - V ^ f.natDegree).natDegree =
      m * V.natDegree + (U - V).natDegree := by
    rw [hm]
    exact power_difference_degree U V hU0 hV0 hdeg hlc hUV m
  have hhigh : C f.leadingCoeff * (U ^ f.natDegree - V ^ f.natDegree) =
      g.eraseLead.comp V - f.eraseLead.comp U := by
    have hleft := congrArg (fun p : K[X] => p.comp U) f.eraseLead_add_C_mul_X_pow
    have hright := congrArg (fun p : K[X] => p.comp V) g.eraseLead_add_C_mul_X_pow
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp] at hleft hright
    rw [← houter, ← houterlc] at hright
    linear_combination hleft - hright + heq
  have hlow : (g.eraseLead.comp V - f.eraseLead.comp U).natDegree ≤
      m * V.natDegree := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · rw [Polynomial.natDegree_comp]
      apply Nat.mul_le_mul_right
      have hg := Polynomial.eraseLead_natDegree_le g
      simpa [← houter, hm] using hg
    · rw [Polynomial.natDegree_comp, hdeg]
      apply Nat.mul_le_mul_right
      have hg := Polynomial.eraseLead_natDegree_le f
      simpa [hm] using hg
  rw [← hhigh, Polynomial.natDegree_C_mul
    (Polynomial.leadingCoeff_ne_zero.mpr hf0), hpow] at hlow
  omega

/-- Equal-degree right components of the same nonconstant outer polynomial
are affinely related. The coefficients are in the original field. -/
theorem same_outer_components_affine (f U V : K[X])
    (hf : 0 < f.natDegree) (hU : 0 < U.natDegree)
    (hdeg : U.natDegree = V.natDegree) (heq : f.comp U = f.comp V) :
    ∃ c b : K, c ≠ 0 ∧ U = C c * V + C b := by
  have hV : 0 < V.natDegree := hdeg ▸ hU
  have hUl : U.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hU)
  have hVl : V.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hV)
  let c : K := U.leadingCoeff / V.leadingCoeff
  have hc : c ≠ 0 := div_ne_zero hUl hVl
  let W : K[X] := C c * V
  let g : K[X] := f.comp (C c⁻¹ * X)
  have hWdeg : U.natDegree = W.natDegree := by
    simpa only [W, Polynomial.natDegree_C_mul hc] using hdeg
  have hWlc : U.leadingCoeff = W.leadingCoeff := by
    simp only [W, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact (div_mul_cancel₀ _ hVl).symm
  have hgcomp : g.comp W = f.comp V := by
    simp only [g, W, Polynomial.comp_assoc, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]
  have hconst : (U - W).natDegree = 0 :=
    constant_difference_of_comp_eq f g U W hf hU hWdeg hWlc (heq.trans hgcomp.symm)
  refine ⟨c, (U - W).coeff 0, hc, ?_⟩
  have hh := Polynomial.eq_C_of_natDegree_eq_zero hconst
  change U = W + C ((U - W).coeff 0)
  linear_combination hh

#print axioms same_outer_components_affine
end DessinsSeparation


/-!
UNVERIFIED INTERNAL DRAFT. No compiler or publication performed by this author.
Lando–Zvonkin, Graphs on Surfaces and Their Applications, Theorem 2.4.15,
printed pp. 125–126: the degree-seven polynomial with derivative
X^3 (X-1)^2 (X-alpha) remembers alpha up to affine changes on both sides.
This is internal infrastructure for the existing separation target only.
-/
namespace DessinsSeparation
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable def rigidPoly (α : K) : K[X] :=
  C (1 / 7 : K) * X ^ 7 - C ((α + 2) / 6) * X ^ 6 +
    C ((2 * α + 1) / 5) * X ^ 5 - C (α / 4) * X ^ 4

noncomputable def rigidDerivative (α : K) : K[X] :=
  X ^ 3 * (X - C 1) ^ 2 * (X - C α)

lemma rigidPoly_derivative (α : K) :
    (rigidPoly α).derivative = rigidDerivative α := by
  have h6 : ((α + 2) / 6) * 6 = α + 2 := div_mul_cancel₀ _ (by norm_num)
  have h5 : ((2 * α + 1) / 5) * 5 = 2 * α + 1 := div_mul_cancel₀ _ (by norm_num)
  have h4 : (α / 4) * 4 = α := div_mul_cancel₀ _ (by norm_num)
  simp only [rigidPoly, derivative_sub, derivative_add, derivative_C_mul_X_pow]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  rw [h6, h5, h4]
  simp only [rigidDerivative, map_add, map_mul, map_one, map_ofNat]
  ring

lemma rigidDerivative_ne_zero (α : K) : rigidDerivative α ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero 1)))
    (X_sub_C_ne_zero α)

lemma rigidDerivative_natDegree (α : K) : (rigidDerivative α).natDegree = 6 := by
  have hX : (X ^ 3 : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h1 : ((X - C 1) ^ 2 : K[X]) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero 1)
  rw [rigidDerivative, natDegree_mul (mul_ne_zero hX h1) (X_sub_C_ne_zero α),
    natDegree_mul hX h1]
  simp only [natDegree_pow, natDegree_X_sub_C, natDegree_X]

lemma rigidPoly_natDegree (α : K) : (rigidPoly α).natDegree = 7 := by
  have h := natDegree_derivative (rigidPoly α)
  rw [rigidPoly_derivative, rigidDerivative_natDegree] at h
  omega

@[simp] lemma rigidPoly_zero (α : K) : (rigidPoly α).eval 0 = 0 := by
  simp [rigidPoly]

lemma rigidPoly_map {L : Type*} [Field L] [CharZero L]
    (σ : K →+* L) (α : K) :
    (rigidPoly α).map σ = rigidPoly (σ α) := by
  simp [rigidPoly, map_ofNat]

lemma rigidPoly_conj (γ : Esquisse.GaloisQ) (α : Esquisse.AlgNum) :
    Esquisse.galoisConj γ (rigidPoly α) = rigidPoly (γ α) := by
  exact rigidPoly_map γ.toAlgHom.toRingHom α

private lemma multiplicity_linear_pow [DecidableEq K] (z t : K) (n : ℕ) :
    ((X - C t) ^ n).rootMultiplicity z = if z = t then n else 0 := by
  classical
  by_cases h : z = t
  · subst z
    simp [rootMultiplicity_X_sub_C_pow]
  · rw [if_neg h]
    apply rootMultiplicity_eq_zero
    change ((X - C t) ^ n).eval z ≠ 0
    simpa using pow_ne_zero n (sub_ne_zero.mpr h)

lemma rigidDerivative_rootMultiplicity [DecidableEq K] (α z : K) :
    (rigidDerivative α).rootMultiplicity z =
      (if z = 0 then 3 else 0) + (if z = 1 then 2 else 0) +
        (if z = α then 1 else 0) := by
  classical
  rw [rigidDerivative, rootMultiplicity_mul (rigidDerivative_ne_zero α)]
  rw [rootMultiplicity_mul
    (mul_ne_zero (pow_ne_zero 3 (X_ne_zero : (X : K[X]) ≠ 0))
      (pow_ne_zero 2 (X_sub_C_ne_zero (1 : K))))]
  have hX : (X ^ 3 : K[X]).rootMultiplicity z = if z = 0 then 3 else 0 := by
    simpa using multiplicity_linear_pow z (0 : K) 3
  rw [hX, multiplicity_linear_pow, rootMultiplicity_X_sub_C]

lemma rigidDerivative_mult_three_iff {α z : K} (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    (rigidDerivative α).rootMultiplicity z = 3 ↔ z = 0 := by
  classical
  rw [rigidDerivative_rootMultiplicity]
  by_cases hz0 : z = 0 <;> by_cases hz1 : z = 1 <;> by_cases hzα : z = α <;>
    simp_all

lemma rigidDerivative_mult_two_iff {α z : K} (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    (rigidDerivative α).rootMultiplicity z = 2 ↔ z = 1 := by
  classical
  rw [rigidDerivative_rootMultiplicity]
  by_cases hz0 : z = 0 <;> by_cases hz1 : z = 1 <;> by_cases hzα : z = α <;>
    simp_all

lemma rigidDerivative_mult_one_iff {α z : K} (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    (rigidDerivative α).rootMultiplicity z = 1 ↔ z = α := by
  classical
  rw [rigidDerivative_rootMultiplicity]
  by_cases hz0 : z = 0 <;> by_cases hz1 : z = 1 <;> by_cases hzα : z = α <;>
    simp_all

private lemma multiplicity_C_mul (q : K[X]) (z c : K) (hc : c ≠ 0) :
    (C c * q).rootMultiplicity z = q.rootMultiplicity z := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) hq)]
    simp

/-- Affine changes of both source and target cannot change the encoded parameter.
The α=0,1 cases are intentionally excluded here and handled separately in separation. -/
lemma rigidPoly_parameter_of_affine
    {α β a b c d : K} (hα0 : α ≠ 0) (hα1 : α ≠ 1)
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (ha : a ≠ 0) (hc : c ≠ 0)
    (h : rigidPoly β = C c * (rigidPoly α).comp (C a * X + C b) + C d) :
    β = α := by
  have hd : rigidDerivative β =
      C (c * a) * (rigidDerivative α).comp (C a * X + C b) := by
    have he := congrArg derivative h
    simp only [rigidPoly_derivative, derivative_add, derivative_mul,
      derivative_C, derivative_comp, derivative_X, zero_mul, zero_add, add_zero,
      mul_one] at he
    simpa only [map_mul, mul_assoc] using he
  have hm (z : K) : (rigidDerivative β).rootMultiplicity z =
      (rigidDerivative α).rootMultiplicity (a * z + b) := by
    rw [hd, multiplicity_C_mul _ _ _ (mul_ne_zero hc ha),
      rootMultiplicity_comp_C_mul_X_add_C _ a b z ha.isUnit]
  have hb : b = 0 := by
    apply (rigidDerivative_mult_three_iff hα0 hα1).mp
    simpa using (hm 0).symm.trans ((rigidDerivative_mult_three_iff hβ0 hβ1).mpr rfl)
  have ha1 : a = 1 := by
    apply (rigidDerivative_mult_two_iff hα0 hα1).mp
    simpa [hb] using (hm 1).symm.trans ((rigidDerivative_mult_two_iff hβ0 hβ1).mpr rfl)
  apply (rigidDerivative_mult_one_iff hα0 hα1).mp
  simpa [hb, ha1] using
    (hm β).symm.trans ((rigidDerivative_mult_one_iff hβ0 hβ1).mpr rfl)

#print axioms rigidPoly_parameter_of_affine
end DessinsSeparation


/- Internal draft for the separation construction. The only imported platform
theorem is the existing polynomial-form Belyi target. Not compiled or published. -/
namespace DessinsSeparation
open Polynomial Esquisse

lemma exists_belyi_postcomposition (p : AlgNum[X]) (hp : 0 < p.natDegree) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧
      IsBelyiPolynomial ((f.map (algebraMap ℚ AlgNum)).comp p) := by
  classical
  have hp' : p.derivative ≠ 0 := derivative_ne_zero.mpr (Nat.ne_of_gt hp)
  let S : Finset AlgNum := p.derivative.roots.toFinset.image p.eval
  obtain ⟨f, hf, hS⟩ := belyi_theorem_polynomial_form S
  refine ⟨f, lt_of_lt_of_le hf.1 natDegree_map_le, ?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hf.1 hp
  · intro z hz
    rw [derivative_comp, eval_mul, eval_comp] at hz
    rw [eval_comp]
    rcases mul_eq_zero.mp hz with hpz | hfz
    · apply hS (p.eval z)
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      exact Multiset.mem_toFinset.mpr ((mem_roots hp').mpr hpz)
    · exact hf.2 (p.eval z) hfz

end DessinsSeparation


/- Complete separation draft. Verification is recorded separately. -/
open Polynomial Esquisse DessinsSeparation

private lemma rational_polynomial_fixed (f : ℚ[X]) (γ : GaloisQ) :
    (f.map (algebraMap ℚ AlgNum)).map γ.toAlgHom.toRingHom =
      f.map (algebraMap ℚ AlgNum) := by
  ext n
  simp only [coeff_map]
  exact γ.commutes (f.coeff n)

theorem solution (α : AlgNum) :
    ∃ P : Polynomial AlgNum, IsBelyiPolynomial P ∧
      ∀ γ : GaloisQ, AffineEquivalent P (galoisConj γ P) → γ α = α := by
  classical
  have hX : IsBelyiPolynomial (X : AlgNum[X]) := by
    constructor
    · simp
    · intro z hz
      simpa using hz
  by_cases hα0 : α = 0
  · subst α
    exact ⟨X, hX, fun γ _ => map_zero γ⟩
  by_cases hα1 : α = 1
  · subst α
    exact ⟨X, hX, fun γ _ => map_one γ⟩
  have hdegree (z : AlgNum) : 0 < (rigidPoly z).natDegree := by
    rw [rigidPoly_natDegree]
    decide
  obtain ⟨f, hfdeg, hfP⟩ := exists_belyi_postcomposition (rigidPoly α) (hdegree α)
  let F : AlgNum[X] := f.map (algebraMap ℚ AlgNum)
  refine ⟨F.comp (rigidPoly α), hfP, ?_⟩
  intro γ hequiv
  obtain ⟨a, b, ha, heq⟩ := hequiv
  have hβ0 : γ α ≠ 0 := by
    intro h
    apply hα0
    apply γ.injective
    simpa using h
  have hβ1 : γ α ≠ 1 := by
    intro h
    apply hα1
    apply γ.injective
    simpa using h
  have hconj : galoisConj γ (F.comp (rigidPoly α)) =
      F.comp (rigidPoly (γ α)) := by
    simp only [galoisConj, map_comp]
    rw [show F.map γ.toAlgHom.toRingHom = F from rational_polynomial_fixed f γ]
    rw [rigidPoly_map]
    rfl
  have hcomp : F.comp (rigidPoly (γ α)) =
      F.comp ((rigidPoly α).comp (C a * X + C b)) := by
    rw [← hconj, heq, comp_assoc]
  have hFdeg : 0 < F.natDegree := by
    dsimp only [F]
    rw [natDegree_map_eq_of_injective (algebraMap ℚ AlgNum).injective]
    exact hfdeg
  have hdeg : (rigidPoly (γ α)).natDegree =
      ((rigidPoly α).comp (C a * X + C b)).natDegree := by
    rw [natDegree_comp, rigidPoly_natDegree, rigidPoly_natDegree,
      natDegree_linear ha, mul_one]
  obtain ⟨c, d, hc, hrigid⟩ := same_outer_components_affine F _ _ hFdeg
    (hdegree (γ α)) hdeg hcomp
  exact rigidPoly_parameter_of_affine hα0 hα1 hβ0 hβ1 ha hc hrigid

#print axioms solution
