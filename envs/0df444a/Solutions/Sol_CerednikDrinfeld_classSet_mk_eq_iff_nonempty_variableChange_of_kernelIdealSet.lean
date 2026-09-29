-- Prove2me | solution 1 for CerednikDrinfeld.classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d9329634-0a5a-5832-acbe-411ba2fea636

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_CerednikDrinfeld_exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange"
namespace K2Criterion
p2m_open "CerednikDrinfeld"

section MapPt

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

noncomputable def mapPt (W : WeierstrassCurve F) (f : F →+* K) :
    W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((WeierstrassCurve.Affine.map_nonsingular W f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right,
        WeierstrassCurve.Affine.Point.add_of_Y_eq (congr_arg f hxy.left) (by
          rw [hxy.right]; exact (WeierstrassCurve.Affine.map_negY f x₂ y₂).symm)]
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        rintro ⟨hx, hy⟩
        rw [WeierstrassCurve.Affine.map_negY] at hy
        exact hxy ⟨f.injective hx, f.injective hy⟩
      rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.add_some hxy']
      simp only [WeierstrassCurve.Affine.map_addX, WeierstrassCurve.Affine.map_addY,
        WeierstrassCurve.Affine.map_slope]

theorem mapPt_zero (W : WeierstrassCurve F) (f : F →+* K) : mapPt W f 0 = 0 := rfl

theorem mapPt_some (W : WeierstrassCurve F) (f : F →+* K) {x y : F} (h : W.toAffine.Nonsingular x y) :
    mapPt W f (.some x y h) =
      .some (f x) (f y) ((WeierstrassCurve.Affine.map_nonsingular W f.injective x y).mpr h) := rfl

theorem mapPt_injective (W : WeierstrassCurve F) (f : F →+* K) : Function.Injective (mapPt W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · exact absurd h (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rw [mapPt_some, mapPt_some] at h
    obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj h
    cases f.injective hx
    cases f.injective hy
    rfl

end MapPt

section Helper

variable {k : Type*} [Field k]

theorem exists_eq_some' {W : WeierstrassCurve k} {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀) (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

end Helper

section Frobenius

variable {κ : Type*} [Field κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

theorem mapPt_iterateFrobenius_mem_rationalHomSet (W : WeierstrassCurve κ) (n : ℕ) :
    (mapPt W (iterateFrobenius κ p n) :
      (W.baseChange κ).toAffine.Point →+ ((W.map (iterateFrobenius κ p n)).baseChange κ).toAffine.Point) ∈
      WeierstrassCurve.rationalHomSet κ W (W.map (iterateFrobenius κ p n)) := by
  right
  refine ⟨C (X ^ p ^ n), 1, X ^ p ^ n, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC (F := κ) κ (1 : κ[X][Y]) x y = 1 := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  have e1 : WeierstrassCurve.evalEvalBC (F := κ) κ (C (X ^ p ^ n) : κ[X][Y]) x y = x ^ p ^ n := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  have e2 : WeierstrassCurve.evalEvalBC (F := κ) κ (X ^ p ^ n : κ[X][Y]) x y = y ^ p ^ n := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  have hP : mapPt W (iterateFrobenius κ p n) (.some x y h) = .some (x ^ p ^ n) (y ^ p ^ n)
      ((WeierstrassCurve.Affine.map_nonsingular W (iterateFrobenius κ p n).injective x y).mpr h) := by
    rw [mapPt_some]; rfl
  exact exists_eq_some' hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem mapPt_iterateFrobenius_some (W : WeierstrassCurve κ) (n : ℕ) {x y : κ} (h : W.toAffine.Nonsingular x y) :
    ∃ h', mapPt W (iterateFrobenius κ p n) (.some x y h) = .some (x ^ p ^ n) (y ^ p ^ n) h' :=
  ⟨_, by rw [mapPt_some]; rfl⟩

end Frobenius

section XRepCalc

variable {κ : Type*} [Field κ]

def XRep (p : ℕ) {W₁ W₂ : WeierstrassCurve κ} (α : W₁.toAffine.Point → W₂.toAffine.Point)
    (u v : κ[X]) (e : ℕ) (B : Set κ) : Prop :=
  ∀ (x y : κ) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
    ∃ (x' y' : κ) (h' : W₂.toAffine.Nonsingular x' y'),
      α (.some x y h) = .some x' y' h' ∧ x' * v.eval (x ^ p ^ e) = u.eval (x ^ p ^ e)

variable {p : ℕ} {W₁ W₂ : WeierstrassCurve κ}

theorem XRep.mono {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e : ℕ} {B B' : Set κ}
    (h : XRep p α u v e B) (hBB' : B ⊆ B') : XRep p α u v e B' :=
  fun x y hxy hx => h x y hxy fun hb => hx (hBB' hb)

theorem XRep.of_expand {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e m : ℕ} {B : Set κ}
    (h : XRep p α (expand κ (p ^ m) u) (expand κ (p ^ m) v) e B) : XRep p α u v (e + m) B := by
  intro x y hxy hx
  obtain ⟨x', y', h', hP, hx'⟩ := h x y hxy hx
  refine ⟨x', y', h', hP, ?_⟩
  rwa [expand_eval, expand_eval, ← pow_mul, ← pow_add] at hx'

theorem XRep.expand {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e m : ℕ} {B : Set κ}
    (h : XRep p α u v (e + m) B) : XRep p α (Polynomial.expand κ (p ^ m) u) (Polynomial.expand κ (p ^ m) v) e B := by
  intro x y hxy hx
  obtain ⟨x', y', h', hP, hx'⟩ := h x y hxy hx
  refine ⟨x', y', h', hP, ?_⟩
  rwa [expand_eval, expand_eval, ← pow_mul, ← pow_add]

theorem exists_nonsingular [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (x : κ) :
    ∃ y : κ, W.toAffine.Nonsingular x y := by
  have hdeg : (W.toAffine.polynomial.map (Polynomial.evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (W.toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.map_evalRingHom_eval] at hy
  exact hy

theorem XRep.mul_eq_mul [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v u' v' : κ[X]} {e : ℕ} {B B' : Set κ} (hB : B.Finite) (hB' : B'.Finite)
    (h : XRep p α u v e B) (h' : XRep p α u' v' e B') : u * v' = v * u' := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : ((iterateFrobenius κ p e) '' (B ∪ B')ᶜ).Infinite :=
    ((hB.union hB').infinite_compl).image (iterateFrobenius κ p e).injective.injOn
  refine hinf.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x₁, y₁, h₁, hP₁, hx₁⟩ := h x y hy hx.1
  obtain ⟨x₂, y₂, h₂, hP₂, hx₂⟩ := h' x y hy hx.2
  rw [hP₁] at hP₂
  obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hP₂
  simp only [Set.mem_setOf_eq, eval_mul, iterateFrobenius_def]
  rw [← hx₁, ← hx₂]
  ring

theorem XRep.false_of_wronskian_ne_zero [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v : κ[X]} {B : Set κ} (hw : wronskian u v ≠ 0) (hB : B.Finite) (h : XRep p α u v 0 B)
    {A D : κ[X]} {g : ℕ} (hg : 1 ≤ g) (hD : D ≠ 0) {B' : Set κ} (hB' : B'.Finite)
    (h' : XRep p α A D g B') : False := by
  have h'' : XRep p α (Polynomial.expand κ (p ^ g) A) (Polynomial.expand κ (p ^ g) D) 0 B' :=
    XRep.expand (by rwa [zero_add])
  have e1 := XRep.mul_eq_mul hB hB' h h''

  have hp : (p : κ[X]) ^ g = 0 := by
    obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
    rw [pow_add, pow_one]
    have : (p : κ[X]) = 0 := by
      rw [← C_eq_natCast, CharP.cast_eq_zero κ p, map_zero]
    rw [this, zero_mul]
  have hdS : derivative (Polynomial.expand κ (p ^ g) D) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have hdR : derivative (Polynomial.expand κ (p ^ g) A) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have e2 := congrArg derivative e1
  rw [derivative_mul, derivative_mul, hdS, hdR, mul_zero, add_zero, mul_zero, add_zero] at e2

  have hS : Polynomial.expand κ (p ^ g) D ≠ 0 := by
    rwa [Ne, expand_eq_zero (pow_pos (Fact.out : p.Prime).pos g)]
  have key : (Polynomial.expand κ (p ^ g) D) ^ 2 * wronskian u v = 0 := by
    rw [wronskian]
    linear_combination (Polynomial.expand κ (p ^ g) D * derivative v) * e1 -
      (Polynomial.expand κ (p ^ g) D * v) * e2
  rcases mul_eq_zero.mp key with h0 | h0
  · exact hS (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  · exact hw h0

theorem isCoprime_of_expand [IsAlgClosed κ] {q : ℕ} (hq : 0 < q) {u v : κ[X]}
    (h : IsCoprime (Polynomial.expand κ q u) (Polynomial.expand κ q v)) : IsCoprime u v := by
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := κ) κ u v).mpr fun a => ?_
  obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a hq
  have := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := κ) κ _ _).mp h b
  simpa only [coe_aeval_eq_eval, expand_eval] using this

theorem exists_XRep_wronskian [DecidableEq κ] [IsAlgClosed κ] [W₁.IsElliptic] [W₂.IsElliptic] [Fact p.Prime] [CharP κ p]
    (α : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (hα0 : α ≠ 0) :
    ∃ (u v : κ[X]) (e : ℕ) (B : Set κ), IsCoprime u v ∧ wronskian u v ≠ 0 ∧ B.Finite ∧ XRep p α u v e B := by
  obtain ⟨u₀, v₀, B, hc₀, hB, hrep₀⟩ := WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet κ W₁ W₂ hα hα0
  have hrep₀' : XRep p α u₀ v₀ 0 B := by
    intro x y h hx
    obtain ⟨x', y', h', hP, hx'⟩ := hrep₀ x y h hx
    exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩

  have hdeg : ∀ (u v : κ[X]) (e : ℕ), IsCoprime u v → XRep p α u v e B → 1 ≤ u.natDegree := by
    intro u v e hc hrep
    have hrep' : XRep p α (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) 0 B :=
      XRep.expand (by rwa [zero_add])
    have hcx : IsCoprime (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) :=
      hc.map (Polynomial.expand κ (p ^ e)).toRingHom
    have hlt := WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α (u := Polynomial.expand κ (p ^ e) u)
      (v := Polynomial.expand κ (p ^ e) v) (B := B) hcx hB (by
        intro x y h hx
        obtain ⟨x', y', h', hP, hx'⟩ := hrep' x y h hx
        exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩)
    rw [natDegree_expand, natDegree_expand] at hlt
    rcases Nat.eq_zero_or_pos u.natDegree with h0 | h0
    · rw [h0, zero_mul] at hlt; exact absurd hlt (Nat.not_lt_zero _)
    · exact h0
  suffices H : ∀ (n : ℕ) (u v : κ[X]) (e : ℕ), u.natDegree ≤ n → IsCoprime u v → XRep p α u v e B →
      ∃ (u v : κ[X]) (e : ℕ) (B : Set κ), IsCoprime u v ∧ wronskian u v ≠ 0 ∧ B.Finite ∧ XRep p α u v e B from
    H _ u₀ v₀ 0 le_rfl hc₀ hrep₀'
  intro n
  induction n with
  | zero =>
    intro u v e hn hc hrep
    exact absurd (le_trans (hdeg u v e hc hrep) hn) (by decide)
  | succ n ih =>
    intro u v e hn hc hrep
    by_cases hw : wronskian u v = 0
    · obtain ⟨hdu, hdv⟩ := hc.wronskian_eq_zero_iff.mp hw
      have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
      set u₁ := contract p u
      set v₁ := contract p v
      have hu : Polynomial.expand κ p u₁ = u := expand_contract p hdu hp0
      have hv : Polynomial.expand κ p v₁ = v := expand_contract p hdv hp0
      have hc₁ : IsCoprime u₁ v₁ := isCoprime_of_expand (Fact.out : p.Prime).pos (by rwa [hu, hv])
      have hrep₁ : XRep p α u₁ v₁ (e + 1) B := XRep.of_expand (m := 1) (by rwa [pow_one, hu, hv])
      refine ih u₁ v₁ (e + 1) ?_ hc₁ hrep₁
      have h1 := hdeg u v e hc hrep
      have hdeg₁ : u.natDegree = u₁.natDegree * p := by rw [← hu, natDegree_expand]
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have : u₁.natDegree < u.natDegree := by
        rw [hdeg₁]
        have hu₁ : 1 ≤ u₁.natDegree := by
          rcases Nat.eq_zero_or_pos u₁.natDegree with h0 | h0
          · rw [hdeg₁, h0, zero_mul] at h1; exact absurd h1 (by decide)
          · exact h0
        nlinarith
      omega
    · exact ⟨u, v, e, B, hc, hw, hB, hrep⟩

end XRepCalc

section Torsion

open WeierstrassCurve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [DecidableEq k]

def Good (W : WeierstrassCurve F) (B : Set k) (P : (W.baseChange k).toAffine.Point) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem finite_setOf_equation (W : WeierstrassCurve F) (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good (W : WeierstrassCurve F) {B : Set k} (hB : B.Finite) :
    {P : (W.baseChange k).toAffine.Point | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : (W.baseChange k).toAffine.Point)
      (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
        {P : (W.baseChange k).toAffine.Point |
          ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

theorem finite_ker {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : IsRationallyRepresented k W₁ W₂ α) : {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine (finite_not_good W₁ hB).subset ?_
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

theorem isOfFinAddOrder_of_apply_eq_zero {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) {P : (W₁.baseChange k).toAffine.Point} (hP : α P = 0) :
    IsOfFinAddOrder P := by
  haveI : Finite α.ker := by
    have := (finite_ker (hα.resolve_left hα0)).to_subtype
    exact Finite.of_equiv {P | α P = 0} (Equiv.refl _)
  have h := isOfFinAddOrder_of_finite (⟨P, hP⟩ : α.ker)
  exact α.ker.subtype.isOfFinAddOrder h

theorem noTorsion_of_hom [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {χ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hχ : χ ∈ rationalHomSet k W₁ W₂) (hχ0 : χ ≠ 0) (p : ℕ)
    (h₁ : ∀ P : (W₁.baseChange k).toAffine.Point, p • P = 0 → P = 0) :
    ∀ P : (W₂.baseChange k).toAffine.Point, p • P = 0 → P = 0 := by
  intro P hP
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hχ hχ0
  obtain ⟨Q, rfl⟩ := hsurj P
  set K : Set (W₁.baseChange k).toAffine.Point := {R | χ R = 0} with hK
  have hKfin : K.Finite := finite_ker (hχ.resolve_left hχ0)
  set S : Set (W₁.baseChange k).toAffine.Point := {R | χ (p • R) = 0} with hS
  have hinj : Set.InjOn (fun R : (W₁.baseChange k).toAffine.Point => p • R) Set.univ := by
    intro R _ R' _ hRR'
    have h0 : p • (R - R') = 0 := by
      simp only [smul_sub, sub_eq_zero]; exact hRR'
    exact sub_eq_zero.mp (h₁ _ h0)
  have hKS : K ⊆ S := by
    intro R hR
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    rw [show χ R = 0 from hR, smul_zero]
  have hmaps : ∀ R ∈ S, (fun R : (W₁.baseChange k).toAffine.Point => p • R) R ∈ K := fun R hR => hR
  have hle : S.ncard ≤ K.ncard :=
    Set.ncard_le_ncard_of_injOn (fun R => p • R) hmaps (hinj.mono (Set.subset_univ _)) hKfin
  have hSfin : S.Finite := by
    have : S = (fun R : (W₁.baseChange k).toAffine.Point => p • R) ⁻¹' K := rfl
    rw [this]
    exact hKfin.preimage (hinj.mono (Set.subset_univ _))
  have hKeq : K = S := Set.eq_of_subset_of_ncard_le hKS hle hSfin
  have hQS : Q ∈ S := by
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    exact hP
  rw [← hKeq] at hQS
  exact hQS

end Torsion

section Core

open WeierstrassCurve

variable {κ : Type*} [Field κ] [DecidableEq κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

abbrev Pt (W : WeierstrassCurve κ) := (W.baseChange κ).toAffine.Point

omit [DecidableEq κ] [IsAlgClosed κ] in
scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve κ) [W.IsElliptic] : (W.baseChange κ).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap κ κ)).IsElliptic)

def SeparatesTorsion (X₀ W : WeierstrassCurve κ) : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ Q : Pt W, ℓ • Q = 0 → Q ≠ 0 → ∃ ρ ∈ rationalHomSet κ W X₀, ρ Q ≠ 0

def HasSeparableHom (X₀ W : WeierstrassCurve κ) : Prop :=
  ∃ ρ ∈ rationalHomSet κ W X₀, ∃ (r s : κ[X]) (B : Set κ),
    IsCoprime r s ∧ wronskian r s ≠ 0 ∧ B.Finite ∧
    ∀ (x y : κ) (h : (W.baseChange κ).toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : κ) (h' : (X₀.baseChange κ).toAffine.Nonsingular x' y'),
        ρ (.some x y h) = .some x' y' h' ∧ x' * s.eval x = r.eval x

omit [IsAlgClosed κ] in

theorem eq_zero_of_forall_apply_eq_zero {X₀ W : WeierstrassCurve κ} [W.IsElliptic]
    (hW : ∀ P : Pt W, p • P = 0 → P = 0) (hT : SeparatesTorsion p X₀ W)
    {Q : Pt W} (hfin : IsOfFinAddOrder Q)
    (hall : ∀ ρ ∈ rationalHomSet κ W X₀, ρ Q = 0) : Q = 0 := by
  by_contra hQ0
  set n := addOrderOf Q with hn
  have hn0 : 0 < n := hfin.addOrderOf_pos
  have hn1 : n ≠ 1 := fun h => hQ0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨m, hm⟩ := hℓn
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; omega
  have hmn : m < n := by
    rw [hm]
    have := hℓ.two_le
    nlinarith [Nat.pos_of_ne_zero hm0]
  set Q₁ := m • Q with hQ₁
  have hQ₁0 : Q₁ ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf hm0 hmn
  have hℓQ₁ : ℓ • Q₁ = 0 := by
    rw [hQ₁, smul_smul, ← hm]
    exact addOrderOf_nsmul_eq_zero Q
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact hQ₁0 (hW _ hℓQ₁)
  obtain ⟨ρ, hρ, hρQ⟩ := hT ℓ hℓ hℓp Q₁ hℓQ₁ hQ₁0
  exact hρQ (by rw [hQ₁, map_nsmul, hall ρ hρ, smul_zero])

variable {p}

theorem core (X₀ W W' : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic] [W'.IsElliptic]
    (hW : ∀ P : Pt W, p • P = 0 → P = 0) (hW' : ∀ P : Pt W', p • P = 0 → P = 0)
    (hT : SeparatesTorsion p X₀ W) (hT' : SeparatesTorsion p X₀ W') (hS : HasSeparableHom X₀ W)
    (χ : Pt X₀ →+ Pt W) (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : Pt X₀ →+ Pt W') (hχ' : χ' ∈ rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (hK : ∀ ρ ∈ rationalHomSet κ W X₀, ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ.comp χ = ρ'.comp χ')
    (hK' : ∀ ρ' ∈ rationalHomSet κ W' X₀, ∃ ρ ∈ rationalHomSet κ W X₀, ρ'.comp χ' = ρ.comp χ)
    {u v : κ[X]} {e : ℕ} {B : Set κ} (hc : IsCoprime u v) (hw : wronskian u v ≠ 0) (hB : B.Finite)
    (hrep : XRep p χ u v e B)
    {u' v' : κ[X]} {e' : ℕ} {B' : Set κ} (hc' : IsCoprime u' v') (hB' : B'.Finite)
    (hrep' : XRep p χ' u' v' e' B') (hee' : e ≤ e') :
    ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W' := by
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0
  have hsurj' := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ' hχ'0

  have hker : ∀ T, χ T = 0 → χ' T = 0 := by
    intro T hT0
    refine eq_zero_of_forall_apply_eq_zero p hW' hT' ?_ ?_
    · exact χ'.isOfFinAddOrder (isOfFinAddOrder_of_apply_eq_zero hχ hχ0 hT0)
    · intro ρ' hρ'
      obtain ⟨ρ, -, hρρ⟩ := hK' ρ' hρ'
      have := congrArg (fun f => f T) hρρ
      simpa only [AddMonoidHom.coe_comp, Function.comp_apply, hT0, map_zero] using this
  have hker' : ∀ T, χ' T = 0 → χ T = 0 := by
    intro T hT0
    refine eq_zero_of_forall_apply_eq_zero p hW hT ?_ ?_
    · exact χ.isOfFinAddOrder (isOfFinAddOrder_of_apply_eq_zero hχ' hχ'0 hT0)
    · intro ρ hρ
      obtain ⟨ρ', -, hρρ⟩ := hK ρ hρ
      have := congrArg (fun f => f T) hρρ
      simpa only [AddMonoidHom.coe_comp, Function.comp_apply, hT0, map_zero] using this

  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hee'
  have hcx : IsCoprime (Polynomial.expand κ (p ^ m) u') (Polynomial.expand κ (p ^ m) v') :=
    hc'.map (Polynomial.expand κ (p ^ m)).toRingHom
  have hrepx : XRep p χ' (Polynomial.expand κ (p ^ m) u') (Polynomial.expand κ (p ^ m) v') e B' :=
    XRep.expand hrep'
  obtain ⟨φ, hφ, hφχ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p X₀ W W'
    hχ hχ' hχ0 hχ'0 hker e hc hw hcx (hB.union hB')
    (fun x y h hx => (hrep.mono Set.subset_union_left) x y h hx)
    (fun x y h hx => (hrepx.mono Set.subset_union_right) x y h hx)

  have hdag : ∀ ρ ∈ rationalHomSet κ W X₀, ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ = ρ'.comp φ := by
    intro ρ hρ
    obtain ⟨ρ', hρ', hρρ'⟩ := hK ρ hρ
    refine ⟨ρ', hρ', ?_⟩
    ext T
    obtain ⟨S, rfl⟩ := hsurj T
    have h1 := congrArg (fun f => f S) hρρ'
    have h2 := congrArg (fun f => f S) hφχ
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at h1 h2 ⊢
    rw [h1]
    exact congrArg ρ' h2
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact hχ'0 (hφχ.trans (AddMonoidHom.zero_comp _))
  have hφinj : ∀ T, φ T = 0 → T = 0 := by
    intro T hT0
    obtain ⟨S, rfl⟩ := hsurj T
    have h2 := congrArg (fun f => f S) hφχ
    exact hker' S (h2.trans hT0)
  have hφsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hφ hφ0

  obtain ⟨uφ, vφ, g, Bφ, hcφ, hwφ, hBφ, hrepφ⟩ := exists_XRep_wronskian (p := p) (W₁ := W) (W₂ := W') φ hφ hφ0

  have hwX : wronskian (X : κ[X]) 1 ≠ 0 := by
    rw [wronskian, derivative_one, derivative_X, mul_zero, one_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  have hg : g = 0 := by
    by_contra hg0
    have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr hg0
    obtain ⟨ρ, hρ, r, s, Br, hcr, hwr, hBr, hrepρ⟩ := hS
    obtain ⟨ρ', hρ', hρρ'⟩ := hdag ρ hρ
    set σ := iterateFrobenius κ p g with hσ
    have hFr := mapPt_iterateFrobenius_mem_rationalHomSet p W g
    obtain ⟨y₀, hy₀⟩ := exists_nonsingular W (0 : κ)
    have hFr0 : mapPt W σ ≠ 0 := by
      intro h0
      have := congrArg (fun f => f (.some 0 y₀ hy₀)) h0
      simp only [mapPt_some, AddMonoidHom.zero_apply] at this
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ this
    obtain ⟨φ₁, hφ₁, hφφ₁⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p
      W (W.map σ) W' hFr hφ hFr0 hφ0 (fun T hT => by rw [mapPt_injective W σ (hT.trans (mapPt_zero W σ).symm), map_zero])
      g (isCoprime_one_right (x := (X : κ[X]))) hwX hcφ hBφ
      (fun x y h _ => by
        obtain ⟨h₂, hP⟩ := mapPt_iterateFrobenius_some p W g h
        exact ⟨_, _, h₂, hP, by rw [eval_one, eval_X, mul_one]⟩)
      (fun x y h hx => hrepφ x y h hx)
    have hβ : ρ'.comp φ₁ ∈ rationalHomSet κ (W.map σ) X₀ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ _ _ _ hφ₁ hρ'
    have hρβ : ρ = (ρ'.comp φ₁).comp (mapPt W σ) := by rw [hρρ', hφφ₁]; rfl
    have hrepρ0 : XRep p ρ r s 0 Br := fun x y h hx => by
      obtain ⟨x', y', h', hP, hx'⟩ := hrepρ x y h hx
      exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩
    have hβ0 : ρ'.comp φ₁ ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := hBr.infinite_compl.nonempty
      obtain ⟨y, hy⟩ := exists_nonsingular W x
      obtain ⟨x', y', h', hP, -⟩ := hrepρ x y hy hx
      have h00 : ρ (.some x y hy) = 0 := by rw [hρβ, h0]; rfl
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ (hP.symm.trans h00)
    obtain ⟨r₁, s₁, B₁, hc₁, hB₁, hrep₁⟩ :=
      WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet κ (W.map σ) X₀ hβ hβ0
    have hB₁' : (σ ⁻¹' B₁).Finite := hB₁.preimage σ.injective.injOn
    have hrepg : XRep p ρ r₁ s₁ g (σ ⁻¹' B₁) := by
      intro x y h hx
      obtain ⟨h₂, hFrP⟩ := mapPt_iterateFrobenius_some p W g h
      obtain ⟨x', y', h', hP, hx'⟩ := hrep₁ (x ^ p ^ g) (y ^ p ^ g) h₂ hx
      refine ⟨x', y', h', ?_, hx'⟩
      rw [hρβ]
      show (ρ'.comp φ₁) (mapPt W σ (.some x y h)) = _
      rw [hFrP]
      exact hP
    by_cases hs₁ : s₁ = 0
    · obtain ⟨x, hx⟩ := hB₁'.infinite_compl.nonempty
      obtain ⟨y, hy⟩ := exists_nonsingular W x
      obtain ⟨x', y', h', -, hx'⟩ := hrepg x y hy hx
      rw [hs₁, eval_zero, mul_zero] at hx'
      have hr₁ : IsUnit r₁ := by rw [hs₁] at hc₁; exact isCoprime_zero_right.mp hc₁
      obtain ⟨c, hc0, hr₁c⟩ := Polynomial.isUnit_iff.mp hr₁
      rw [← hr₁c, eval_C] at hx'
      exact hc0.ne_zero hx'.symm
    · exact XRep.false_of_wronskian_ne_zero hwr hBr hrepρ0 hg1 hs₁ hB₁' hrepg

  subst hg
  have hid0 : (AddMonoidHom.id (Pt W)) ≠ 0 := by
    intro h0
    obtain ⟨y₀, hy₀⟩ := exists_nonsingular W (0 : κ)
    have := congrArg (fun f => f (.some 0 y₀ hy₀)) h0
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ this
  obtain ⟨ε, hε, hidε⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p
    W W' W hφ (WeierstrassCurve.id_mem_rationalHomSet κ W) hφ0 hid0 (fun T hT => hφinj T hT)
    0 hcφ hwφ (isCoprime_one_right (x := (X : κ[X]))) hBφ
    (fun x y h hx => hrepφ x y h hx)
    (fun x y h _ => ⟨x, y, h, rfl, by simp only [eval_one, eval_X, mul_one, pow_zero, pow_one]⟩)
  have h1 : ε.comp φ = AddMonoidHom.id _ := hidε.symm
  have h2 : φ.comp ε = AddMonoidHom.id _ := by
    ext T
    obtain ⟨S, rfl⟩ := hφsurj T
    exact (congrArg φ (congrArg (fun f => f S) hidε)).symm
  exact WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet κ W W' φ hφ ε hε h1 h2

theorem iso_of_kernel_match (X₀ W W' : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic] [W'.IsElliptic]
    (hW : ∀ P : Pt W, p • P = 0 → P = 0) (hW' : ∀ P : Pt W', p • P = 0 → P = 0)
    (hT : SeparatesTorsion p X₀ W) (hT' : SeparatesTorsion p X₀ W')
    (hS : HasSeparableHom X₀ W) (hS' : HasSeparableHom X₀ W')
    (χ : Pt X₀ →+ Pt W) (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : Pt X₀ →+ Pt W') (hχ' : χ' ∈ rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (hK : ∀ ρ ∈ rationalHomSet κ W X₀, ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ.comp χ = ρ'.comp χ')
    (hK' : ∀ ρ' ∈ rationalHomSet κ W' X₀, ∃ ρ ∈ rationalHomSet κ W X₀, ρ'.comp χ' = ρ.comp χ) :
    ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W' := by
  obtain ⟨u, v, e, B, hc, hw, hB, hrep⟩ := exists_XRep_wronskian (p := p) (W₁ := X₀) (W₂ := W) χ hχ hχ0
  obtain ⟨u', v', e', B', hc', hw', hB', hrep'⟩ :=
    exists_XRep_wronskian (p := p) (W₁ := X₀) (W₂ := W') χ' hχ' hχ'0
  rcases le_total e e' with h | h
  · exact core X₀ W W' hW hW' hT hT' hS χ hχ hχ0 χ' hχ' hχ'0 hK hK' hc hw hB hrep hc' hB' hrep' h
  · obtain ⟨γ, hγ⟩ := core X₀ W' W hW' hW hT' hT hS' χ' hχ' hχ'0 χ hχ hχ0 hK' hK hc' hw' hB' hrep' hc hB hrep h
    exact ⟨γ⁻¹, by rw [← hγ, smul_smul, inv_mul_cancel, one_smul]⟩

end Core

section HomSet

open WeierstrassCurve

variable {κ : Type*} [Field κ] [DecidableEq κ]

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve κ}
    {α : (W₁.baseChange κ).toAffine.Point →+ (W₂.baseChange κ).toAffine.Point} (hα : α ∈ rationalHomSet κ W₁ W₂) :
    -α ∈ rationalHomSet κ W₁ W₂ := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet κ W₁ W₂
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX, B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  have hbc : ∀ q : κ[X][Y], evalEvalBC (F := κ) κ q x y = q.evalEval x y := by
    intro q; simp [evalEvalBC, Polynomial.map_id]
  refine ⟨hdX, by rw [hbc, evalEval_mul]; rw [hbc] at hdX hdY; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (evalEvalBC (F := κ) κ nX x y / evalEvalBC (F := κ) κ dX x y)
        ((W₂.baseChange κ).toAffine.negY (evalEvalBC (F := κ) κ nX x y / evalEvalBC (F := κ) κ dX x y)
          (evalEvalBC (F := κ) κ nY x y / evalEvalBC (F := κ) κ dY x y))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_eq_some' hneg rfl ?_
  simp only [hbc] at hdX hdY ⊢
  simp only [Affine.negY, evalEval_sub, evalEval_neg, evalEval_mul, evalEval_C, eval_C]
  change -(nY.evalEval x y / dY.evalEval x y) - W₂.a₁ * (nX.evalEval x y / dX.evalEval x y) - W₂.a₃ = _
  field_simp

theorem nsmul_mem_rationalHomSet [IsAlgClosed κ] {W₁ W₂ : WeierstrassCurve κ} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange κ).toAffine.Point →+ (W₂.baseChange κ).toAffine.Point} (hα : α ∈ rationalHomSet κ W₁ W₂)
    (n : ℕ) : n • α ∈ rationalHomSet κ W₁ W₂ := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet κ W₁ W₂
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet κ W₁ W₂ ih hα

theorem mem_rationalHomSet_of_mem_rationalEndSubring [IsAlgClosed κ] {W : WeierstrassCurve κ} [W.IsElliptic]
    {f : AddMonoid.End (W.baseChange κ).toAffine.Point} (hf : f ∈ rationalEndSubring κ W) :
    (f : (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) ∈ rationalHomSet κ W W := by
  induction hf using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet κ W W
  | one => exact id_mem_rationalHomSet κ W
  | add x y _ _ hx hy => exact add_mem_rationalHomSet κ W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet hx
  | mul x y _ _ hx hy => exact comp_mem_rationalHomSet κ W W W hy hx

omit [DecidableEq κ] in
theorem infinite_point [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] :
    Infinite (W.baseChange κ).toAffine.Point := by
  choose f hf using exists_nonsingular (W.baseChange κ)
  refine Infinite.of_injective (fun x : κ => (Affine.Point.some x (f x) (hf x) : (W.baseChange κ).toAffine.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem exists_nsmul_ne_zero [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∀ P : (W.baseChange κ).toAffine.Point, p • P = 0 → P = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ P : (W.baseChange κ).toAffine.Point, N • P ≠ 0 := by
  obtain ⟨k, m, hm, hNkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p (Fact.out : p.Prime).ne_one
  have hstrip : ∀ (j : ℕ) (P : (W.baseChange κ).toAffine.Point), (p ^ j) • P = 0 → P = 0 := by
    intro j
    induction j with
    | zero => intro P hP; simpa using hP
    | succ j ih =>
      intro P hP
      rw [pow_succ, mul_smul] at hP
      exact hW P (ih _ hP)
  by_contra hall
  push Not at hall
  have hm0 : m ≠ 0 := by rintro rfl; simp at hNkm; exact hN hNkm
  have hmκ : ((m : ℕ) : κ) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff κ p m).mp h)
  have htors : ∀ P : (W.baseChange κ).toAffine.Point, P ∈ Submodule.torsionBy ℤ _ (m : ℤ) := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    have h1 : (p ^ k) • (m • P) = 0 := by
      rw [← mul_smul, ← hNkm]
      exact hall P
    have h2 := hstrip k _ h1
    rw [natCast_zsmul]
    exact h2
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W (n := m) hmκ
  haveI : Finite ↥(Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (m : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact pow_ne_zero 2 hm0
  haveI := infinite_point W
  haveI : Finite (W.baseChange κ).toAffine.Point :=
    Finite.of_injective (fun P => (⟨P, htors P⟩ : ↥(Submodule.torsionBy ℤ _ (m : ℤ))))
      (fun P Q h => congrArg Subtype.val h)
  exact not_finite (W.baseChange κ).toAffine.Point

end HomSet

section Assembly

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain WeierstrassCurve

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])

theorem ofFiniteIdele_mul_of_mem (hΛ : IsOrder Λ)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    Submodule.ofFiniteIdele Λ (x * u) = Submodule.ofFiniteIdele Λ x :=
  ((Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop x (x * u)).mpr
    (by rwa [inv_mul_cancel_left])).symm

theorem exists_ofFiniteIdele_eq_smul_of_mk_eq_mk (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h : ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x') :
    ∃ δ : (ℍ[ℚ, a, b])ˣ, Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x := by
  obtain ⟨g, hg, u, hu, rfl⟩ := (DoubleCoset.eq _ _ _ _).mp h
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hg
  exact ⟨δ, by rw [ofFiniteIdele_mul_of_mem Λ hΛ _ u hu, Submodule.ofFiniteIdele_diagonal_mul]⟩

theorem exists_mem_stabilizer_of_ofFiniteIdele_eq_smul (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (δ : (ℍ[ℚ, a, b])ˣ)
    (h : Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, x' = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u := by
  rw [← Submodule.ofFiniteIdele_diagonal_mul] at h
  have hu := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop
    (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) x').mp h.symm
  exact ⟨_, hu, by rw [mul_inv_cancel_left]⟩

theorem mk_eq_mk_of_ofFiniteIdele_eq_smul (hΛ : IsOrder Λ)
    {x x' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (δ : (ℍ[ℚ, a, b])ˣ)
    (h : Submodule.ofFiniteIdele Λ x' = δ • Submodule.ofFiniteIdele Λ x) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x' = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x := by
  obtain ⟨u, hu, rfl⟩ := exists_mem_stabilizer_of_ofFiniteIdele_eq_smul Λ hΛ δ h
  exact ((DoubleCoset.eq _ _ _ _).mpr ⟨_, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, u, hu, rfl⟩).symm

variable {Λ}

theorem mem_smul_iff (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔ ∃ w ∈ I, (d : ℍ[ℚ, a, b]) * w = z :=
  Submodule.mem_smul_pointwise_iff_exists z d I

theorem image_eq_image_mul_of_smul {K K' : Set ℍ[ℚ, a, b]} {I J : Submodule ℤ ℍ[ℚ, a, b]}
    (d d' δ : (ℍ[ℚ, a, b])ˣ) (hJ : J = δ • I)
    (hK : K = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hK' : K' = star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    K' = (· * star ((d' * δ * d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) '' K := by
  subst hK hK' hJ
  have key : ∀ w : ℍ[ℚ, a, b], star ((d : ℍ[ℚ, a, b]) * w) * star ((d' * δ * d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) =
      star ((d' : ℍ[ℚ, a, b]) * ((δ : ℍ[ℚ, a, b]) * w)) := by
    intro w
    rw [← star_mul, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_smul_iff d' _ w').mp hw'
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff δ _ t).mp ht
    exact ⟨star ((d : ℍ[ℚ, a, b]) * w), ⟨_, (mem_smul_iff d I _).mpr ⟨w, hw, rfl⟩, rfl⟩, key w⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff d I v).mp hv
    exact ⟨_, (mem_smul_iff d' _ _).mpr ⟨_, (mem_smul_iff δ I _).mpr ⟨w, hw, rfl⟩, rfl⟩, (key w).symm⟩

theorem exists_smul_of_image_eq_image_mul {K K' : Set ℍ[ℚ, a, b]} {I J : Submodule ℤ ℍ[ℚ, a, b]}
    (d d' c : (ℍ[ℚ, a, b])ˣ)
    (hK : K = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hK' : K' = star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (h : K' = (· * (c : ℍ[ℚ, a, b])) '' K) : J = (d'⁻¹ * star c * d) • I := by
  subst hK hK'
  have key : ∀ w : ℍ[ℚ, a, b], star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) =
      star ((star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w) := by
    intro w
    simp only [star_mul, Units.coe_star, star_star, mul_assoc]

  have h1 : ∀ t ∈ J, ∃ w ∈ I, (d' : ℍ[ℚ, a, b]) * t = (star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w := by
    intro t ht
    have : star ((d' : ℍ[ℚ, a, b]) * t) ∈ star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) :=
      ⟨_, (mem_smul_iff d' J _).mpr ⟨t, ht, rfl⟩, rfl⟩
    rw [h] at this
    obtain ⟨_, ⟨v, hv, rfl⟩, hz⟩ := this
    obtain ⟨w, hw, rfl⟩ := (mem_smul_iff d I v).mp hv
    have hz' : star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) = star ((d' : ℍ[ℚ, a, b]) * t) := hz
    rw [key] at hz'
    exact ⟨w, hw, (star_injective hz').symm⟩

  have h2 : ∀ w ∈ I, ∃ t ∈ J, (d' : ℍ[ℚ, a, b]) * t = (star c : (ℍ[ℚ, a, b])ˣ) * (d : ℍ[ℚ, a, b]) * w := by
    intro w hw
    have : star ((d : ℍ[ℚ, a, b]) * w) * (c : ℍ[ℚ, a, b]) ∈
        (· * (c : ℍ[ℚ, a, b])) '' (star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :=
      ⟨_, ⟨_, (mem_smul_iff d I _).mpr ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [← h] at this
    obtain ⟨_, hv, hz⟩ := this
    obtain ⟨t, ht, rfl⟩ := (mem_smul_iff d' J _).mp hv
    rw [key] at hz
    exact ⟨t, ht, star_injective hz⟩
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := h1 z hz
    have hz' : z = ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc ((star c : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]),
        ← hzw, Units.inv_mul_cancel_left]
    rw [hz']
    exact Submodule.smul_mem_pointwise_smul w _ I hw
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z _ I).mp hz
    obtain ⟨t, ht, htw⟩ := h2 w hw
    have hz' : ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w = t := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc ((star c : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]),
        ← htw, Units.inv_mul_cancel_left]
    show ((d'⁻¹ * star c * d : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * w ∈ J
    rw [hz']
    exact ht

theorem forward {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (χ : Pt X₀ →+ Pt W) (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (χ' : Pt X₀ →+ Pt W') (hχ' : χ' ∈ rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0)
    (c : ℍ[ℚ, a, b]) (hc0 : c ≠ 0)
    (hmul : θ '' kernelIdealSet κ X₀ W' χ' = (· * c) '' (θ '' kernelIdealSet κ X₀ W χ)) :
    ∃ γ : VariableChange κ, γ • W = W' := by
  have hX₀ : ∀ P : Pt X₀, q' • P = 0 → P = 0 := fun P hP => hss P hP
  have hW : ∀ P : Pt W, q' • P = 0 → P = 0 := noTorsion_of_hom hχ hχ0 q' hX₀
  have hW' : ∀ P : Pt W', q' • P = 0 → P = 0 := noTorsion_of_hom hχ' hχ'0 q' hX₀

  have hT : SeparatesTorsion q' X₀ W := fun ℓ hℓ hℓq Q hQ hQ0 =>
    WeierstrassCurve.exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero q' X₀ a b Λ hΛ θ hθ hθΛ W χ hχ hχ0
      ℓ hℓ hℓq Q hQ hQ0
  have hT' : SeparatesTorsion q' X₀ W' := fun ℓ hℓ hℓq Q hQ hQ0 =>
    WeierstrassCurve.exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero q' X₀ a b Λ hΛ θ hθ hθΛ W' χ' hχ'
      hχ'0 ℓ hℓ hℓq Q hQ hQ0
  have hS : HasSeparableHom X₀ W :=
    WeierstrassCurve.exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero q' X₀ W hss χ hχ hχ0
  have hS' : HasSeparableHom X₀ W' :=
    WeierstrassCurve.exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero q' X₀ W' hss χ' hχ' hχ'0

  obtain ⟨N, hN0, hNc⟩ := exists_natCast_smul_mem_of_mem_span (Λ := Λ) (y := c) (by rw [hΛ.spanTop]; trivial)
  have hNc' : ((N : ℕ) : ℤ) • c ∈ Set.range θ := by rw [hθΛ]; exact hNc
  obtain ⟨γ₀, hγ₀⟩ := hNc'
  have hNc0 : ((N : ℕ) : ℤ) • c ≠ 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    exact smul_ne_zero (Nat.cast_ne_zero.mpr hN0) hc0
  set g : Pt X₀ →+ Pt X₀ := (γ₀ : AddMonoid.End (Pt X₀)) with hgdef
  have hg : g ∈ rationalHomSet κ X₀ X₀ := mem_rationalHomSet_of_mem_rationalEndSubring γ₀.2
  have hg0 : g ≠ 0 := by
    intro h0
    apply hNc0
    rw [← hγ₀]
    have : γ₀ = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hgsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hg hg0

  set χ₁ : Pt X₀ →+ Pt W := χ.comp g with hχ₁def
  have hχ₁ : χ₁ ∈ rationalHomSet κ X₀ W := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ X₀ W hg hχ
  have hχ₁0 : χ₁ ≠ 0 := by
    intro h0
    apply hχ0
    ext T
    obtain ⟨S, rfl⟩ := hgsurj T
    exact congrArg (fun f => f S) h0
  set χ₁' : Pt X₀ →+ Pt W' := N • χ' with hχ₁'def
  have hχ₁' : χ₁' ∈ rationalHomSet κ X₀ W' := nsmul_mem_rationalHomSet hχ' N
  have hχ₁'0 : χ₁' ≠ 0 := by
    obtain ⟨R, hR⟩ := exists_nsmul_ne_zero q' W' hW' hN0
    obtain ⟨S, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ' hχ'0 R
    intro h0
    apply hR
    have := congrArg (fun f => f S) h0
    simpa only [hχ₁'def, AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply] using this

  have step : ∀ (aE a' : rationalEndSubring κ X₀), θ a' = θ aE * c →
      ((aE : AddMonoid.End (Pt X₀)) : Pt X₀ → Pt X₀) ∘ g = fun P => N • (a' : AddMonoid.End (Pt X₀)) P := by
    intro aE a' hθa'
    have hθeq : θ (aE * γ₀) = θ ((N : rationalEndSubring κ X₀) * a') := by
      rw [map_mul, map_mul, map_natCast, hγ₀, hθa', zsmul_eq_mul, Int.cast_natCast, ← mul_assoc,
        ← Nat.cast_comm N (θ aE), mul_assoc]
    have hinj : aE * γ₀ = (N : rationalEndSubring κ X₀) * a' := hθ hθeq
    have hval := congrArg (fun t : rationalEndSubring κ X₀ => ((t : AddMonoid.End (Pt X₀)) : Pt X₀ → Pt X₀)) hinj
    funext P
    have hP := congrFun hval P
    simp only [Subring.coe_mul, SubringClass.coe_natCast] at hP
    exact hP
  have hK : ∀ ρ ∈ rationalHomSet κ W X₀, ∃ ρ' ∈ rationalHomSet κ W' X₀, ρ.comp χ₁ = ρ'.comp χ₁' := by
    intro ρ hρ
    let aE : rationalEndSubring κ X₀ :=
      ⟨ρ.comp χ, Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ hρ)⟩
    have haK : aE ∈ kernelIdealSet κ X₀ W χ := ⟨ρ, hρ, rfl⟩
    have hmem : θ aE * c ∈ θ '' kernelIdealSet κ X₀ W' χ' := by rw [hmul]; exact ⟨θ aE, ⟨aE, haK, rfl⟩, rfl⟩
    obtain ⟨a', ⟨ρ', hρ', ha'⟩, hθa'⟩ := hmem
    refine ⟨ρ', hρ', ?_⟩
    have := step aE a' hθa'
    ext P
    have hP := congrFun this P
    rw [ha'] at hP
    simp only [hχ₁def, hχ₁'def, Function.comp_apply, AddMonoidHom.coe_comp, AddMonoidHom.nsmul_apply,
      map_nsmul] at hP ⊢
    exact hP
  have hK' : ∀ ρ' ∈ rationalHomSet κ W' X₀, ∃ ρ ∈ rationalHomSet κ W X₀, ρ'.comp χ₁' = ρ.comp χ₁ := by
    intro ρ' hρ'
    let a' : rationalEndSubring κ X₀ :=
      ⟨ρ'.comp χ', Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W' X₀ hχ' hρ')⟩
    have haK' : a' ∈ kernelIdealSet κ X₀ W' χ' := ⟨ρ', hρ', rfl⟩
    have hmem : θ a' ∈ (· * c) '' (θ '' kernelIdealSet κ X₀ W χ) := by rw [← hmul]; exact ⟨a', haK', rfl⟩
    obtain ⟨_, ⟨aE, ⟨ρ, hρ, haE⟩, rfl⟩, hθa'⟩ := hmem
    refine ⟨ρ, hρ, ?_⟩
    have := step aE a' hθa'.symm
    ext P
    have hP := congrFun this P
    rw [haE] at hP
    have hP' : ρ (χ (g P)) = N • ρ' (χ' P) := hP
    simp only [hχ₁def, hχ₁'def, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.nsmul_apply, map_nsmul]
    exact hP'.symm
  exact iso_of_kernel_match (p := q') X₀ W W' hW hW' hT hT' hS hS' χ₁ hχ₁ hχ₁0 χ₁' hχ₁' hχ₁'0 hK hK'

end Assembly

end CerednikDrinfeld.K2Criterion
p2m_reactivate "P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet.CerednikDrinfeld P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet.CerednikDrinfeld.K2Criterion"
p2m_reactivate "P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet.CerednikDrinfeld"

open scoped Quaternion TensorProduct NumberField Pointwise in
open QuaternionAlgebra _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet.CerednikDrinfeld ModularCurve CerednikDrinfeld.K2Criterion in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (χ' : (X₀.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hχ' : χ' ∈ WeierstrassCurve.rationalHomSet κ X₀ W') (hχ'0 : χ' ≠ 0) (d' : (ℍ[ℚ, a, b])ˣ)
    (hχ'K : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W' χ') =
      star '' ((d' • Submodule.ofFiniteIdele Λ y : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x = ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) y ↔
      ∃ γ : WeierstrassCurve.VariableChange κ, γ • W = W' := by
  constructor
  · intro hxy
    obtain ⟨δ, hδ⟩ := exists_ofFiniteIdele_eq_smul_of_mk_eq_mk Λ hΛ.isOrder hxy
    have hmul := image_eq_image_mul_of_smul d d' δ hδ hχK hχ'K
    exact forward q' X₀ hss Λ hΛ.isOrder θ hθ hθΛ W W' χ hχ hχ0 χ' hχ' hχ'0 _
      (by rw [← Units.coe_star]; exact Units.ne_zero _) hmul
  · intro hW
    obtain ⟨c, hc⟩ :=
      CerednikDrinfeld.exists_units_image_kernelIdealSet_eq_image_mul_of_exists_variableChange q' X₀ hss a b
        hdef.neg_left hdef.neg_right θ hθ W W' χ hχ hχ0 χ' hχ' hχ'0 hW
    have hJ := exists_smul_of_image_eq_image_mul d d' c hχK hχ'K hc
    exact (mk_eq_mk_of_ofFiniteIdele_eq_smul Λ hΛ.isOrder _ hJ).symm

end S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet
end P2MW
export P2MW.S_CerednikDrinfeld_classSet_mk_eq_iff_nonempty_variableChange_of_kernelIdealSet (solution)
