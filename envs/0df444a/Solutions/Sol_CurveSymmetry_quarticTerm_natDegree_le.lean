-- Prove2me | solution 1 for CurveSymmetry.quarticTerm_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:38.802575+00:00
-- url     : https://prove2.me/submissions/8abe5906-59d9-490d-87dc-2a5c6ed9a5c5

-- Solution generated from lean/FermatGenus.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
import Theorems.Thm_CurveSymmetry_dualS_inv_notMem
import Theorems.Thm_CurveSymmetry_fermat_regularAt_infinity_iff
import Theorems.Thm_CurveSymmetry_kummerLocal_poly_inv_mem
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Ring
variable (n : ℕ) (f : ℂ[X])
lemma kummerRingMap_root :
    kummerRingMap n f (AdjoinRoot.root (kummerPoly n f)) = AdjoinRoot.root (kummerRat n f) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _
end Ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
lemma kummerField_polynomial_injective :
    Function.Injective (algebraMap ℂ[X] (KummerField n f)) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) (KummerField n f)]
  exact (algebraMap (RatFunc ℂ) (KummerField n f)).injective.comp
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma kummerLocal_ringElem_mem (r : KummerRing n f) :
    algebraMap (KummerRing n f) (KummerField n f) r ∈ kummerLocalRing a b hb :=
  Subalgebra.algebraMap_mem _ _
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma kummerLocal_poly_mem (p : ℂ[X]) :
    algebraMap ℂ[X] (KummerField n f) p ∈ kummerLocalRing a b hb := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (KummerRing n f) (KummerField n f)]
  exact kummerLocal_ringElem_mem a b hb _
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma kummerLocal_root_mem :
    AdjoinRoot.root (kummerRat n f) ∈ kummerLocalRing a b hb := by
  rw [← kummerRingMap_root]
  exact kummerLocal_ringElem_mem a b hb _
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
lemma fermatDual_eval_zero : fermatDual.eval 0 ≠ 0 := by
  simp [fermatDual]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- The chart coordinate `s` lies in the local ring at `(0, ζ)`. -/
lemma dualS_mem : dualS ∈ dualLocalRing := by
  rw [dualS, kummerX]
  exact kummerLocal_poly_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow X
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- The chart coordinate `r` is a unit there: `r(0, ζ) = ζ ≠ 0`. -/
lemma dualR_mem_and_inv_mem : dualR ∈ dualLocalRing ∧ dualR⁻¹ ∈ dualLocalRing := by
  refine ⟨kummerLocal_root_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow, ?_⟩
  have hζ : fermatZeta ≠ 0 := by
    intro h0
    have := fermatZeta_pow
    rw [h0, zero_pow (by norm_num)] at this
    exact fermatDual_eval_zero this.symm
  have hmem : AdjoinRoot.root (kummerPoly 4 fermatDual) ∈
      (RingHom.ker (kummerEval 4 fermatDual 0 fermatZeta fermatZeta_pow)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, kummerEval_root]
    exact hζ
  obtain ⟨v, hv⟩ := (IsLocalization.map_units dualLocalRing ⟨_, hmem⟩).exists_right_inv
  have hcoe : dualR * (v : K₄') = 1 := by
    have hc1 := congrArg (fun z : dualLocalRing => (z : K₄')) hv
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at hc1
    show AdjoinRoot.root (kummerRat 4 fermatDual) * (v : K₄') = 1
    rw [← kummerRingMap_root]
    exact hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact v.2
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
lemma dualR_ne_zero : dualR ≠ 0 := by
  intro h
  have h4 : dualR ^ 4 = algebraMap ℂ[X] K₄' fermatDual := kummerRoot_pow 4 fermatDual
  rw [h, zero_pow (by norm_num)] at h4
  have h0 : fermatDual = 0 :=
    kummerField_polynomial_injective (n := 4) (f := fermatDual) (h4.symm.trans (map_zero _).symm)
  have hd := fermatDual_natDegree
  rw [h0, natDegree_zero] at hd
  exact absurd hd (by norm_num)
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- A polynomial in `x`, read in the chart at infinity: `p(1/s) = rev(p)(s)·s^(−deg p)`. -/
lemma fermatInfinityMap_poly (p : ℂ[X]) :
    fermatInfinityMap (algebraMap ℂ[X] K₄ p) =
      algebraMap ℂ[X] K₄' p.reverse * dualS⁻¹ ^ p.natDegree := by
  let _ : Invertible (dualS⁻¹) := invertibleOfNonzero (inv_ne_zero dualS_ne_zero)
  have hrev : eval₂ (algebraMap ℂ K₄') dualS p.reverse = algebraMap ℂ[X] K₄' p.reverse :=
    eval₂_algebraMap_X p.reverse (IsScalarTower.toAlgHom ℂ ℂ[X] K₄')
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄, fermatInfinityMap_of, ratInv_algebraMap,
    ← aeval_algebraMap_apply, map_inv₀, ← dualS_eq, aeval_def,
    ← eval₂_reverse_mul_pow (algebraMap ℂ K₄') dualS⁻¹ p, invOf_eq_inv, inv_inv, hrev]
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
theorem solution {p : ℂ[X]} (hp : p ≠ 0) {j : ℕ}
    (h : quarticTerm p j • KaehlerDifferential.D ℂ K₄ quarticX ∈ regularAt fermatInfinityPlace) :
    p.natDegree + j ≤ 1 := by
  rw [fermat_regularAt_infinity_iff] at h
  by_contra hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ p.natDegree + j by omega)
  have ha0 : algebraMap ℂ[X] K₄' p.reverse ≠ 0 :=
    (map_ne_zero_iff _ (kummerField_polynomial_injective (n := 4) (f := fermatDual))).mpr
      (reverse_eq_zero.not.mpr hp)
  have hainv : (algebraMap ℂ[X] K₄' p.reverse)⁻¹ ∈ dualLocalRing :=
    kummerLocal_poly_inv_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow p.reverse
      (by rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hp)
  obtain ⟨hr, hrinv⟩ := dualR_mem_and_inv_mem
  have hr0 := dualR_ne_zero
  have hs0 := dualS_ne_zero
  have hφ : fermatInfinityMap (quarticTerm p j) * dualS⁻¹ ^ 2 =
      algebraMap ℂ[X] K₄' p.reverse * dualR ^ j * dualR⁻¹ ^ 3 * dualS ^ 3 *
        dualS⁻¹ ^ (p.natDegree + j + 2) := by
    rw [quarticTerm, map_mul, map_mul, map_pow, map_pow, map_inv₀, fermatInfinityMap_poly,
      fermatInfinityMap_root, mul_inv, inv_inv]
    ring
  -- `s³·s^(−(deg p + j + 2)) = s^(−(k + 1))`
  have hsk : dualS ^ 3 * dualS⁻¹ ^ (p.natDegree + j + 2) = dualS⁻¹ ^ (k + 1) := by
    rw [hk, show 2 + k + 2 = 3 + (k + 1) by omega, pow_add, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs0, one_pow, one_mul]
  -- the unit `rev(p)(s)·rʲ·r⁻³` and its inverse
  have hU : ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * dualR⁻¹ ^ j * dualR ^ 3) *
      (algebraMap ℂ[X] K₄' p.reverse * dualR ^ j * dualR⁻¹ ^ 3) = 1 := by
    calc _ = ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * algebraMap ℂ[X] K₄' p.reverse) *
          (dualR⁻¹ * dualR) ^ j * (dualR * dualR⁻¹) ^ 3 := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ ha0, inv_mul_cancel₀ hr0, mul_inv_cancel₀ hr0]
        simp
  have hk1 : dualS⁻¹ ^ (k + 1) ∈ dualLocalRing := by
    have e : dualS⁻¹ ^ (k + 1) =
        ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * dualR⁻¹ ^ j * dualR ^ 3) *
          (fermatInfinityMap (quarticTerm p j) * dualS⁻¹ ^ 2) := by
      rw [hφ, mul_assoc _ (dualS ^ 3), hsk, ← mul_assoc, hU, one_mul]
    rw [e]
    exact mul_mem (mul_mem (mul_mem hainv (pow_mem hrinv j)) (pow_mem hr 3)) h
  have hC : dualS⁻¹ = dualS⁻¹ ^ (k + 1) * dualS ^ k := by
    rw [pow_succ', mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, mul_one]
  apply dualS_inv_notMem
  rw [hC]
  exact mul_mem hk1 (pow_mem dualS_mem k)
end

#print axioms solution
