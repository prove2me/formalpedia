-- Prove2me | solution 1 for CurveSymmetry.quarticHolo_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:29.932549+00:00
-- url     : https://prove2.me/submissions/8bd98d5c-8353-4fd2-b81d-5b1d09622924

-- Solution generated from lean/FermatHolomorphic.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section BaseChange
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]
omit [Unique ι] in
@[simp] lemma kaehlerBasisOfEtale_apply (b : Module.Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfEtale, Module.Basis.baseChange_apply,
    KaehlerDifferential.mapBaseChange_tmul]
end BaseChange
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma polynomialKaehlerBasis_apply (i : Unit) :
    polynomialKaehlerBasis i = KaehlerDifferential.D ℂ ℂ[X] X := by
  simp [polynomialKaehlerBasis, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma ratFuncKaehlerBasis_apply (i : Unit) :
    ratFuncKaehlerBasis i = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  rw [ratFuncKaehlerBasis, kaehlerBasisOfEtale_apply, polynomialKaehlerBasis_apply,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
@[simp] lemma kummerKaehlerBasis_apply (i : Unit) :
    kummerKaehlerBasis n f i = KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  rw [kummerKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, kummerX_eq]
end Field
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
theorem kummer_D_x_ne_zero : KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) ≠ 0 := by
  have := (kummerKaehlerBasis n f).ne_zero (default : Unit)
  rwa [kummerKaehlerBasis_apply] at this
end Field
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quartic_polynomial_injective : Function.Injective (algebraMap ℂ[X] K₄) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) K₄]
  exact (algebraMap (RatFunc ℂ) K₄).injective.comp (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticY_ne_zero : quarticY ≠ 0 := by
  intro h0
  have h := kummerRoot_pow 4 fermatQuartic
  rw [show AdjoinRoot.root (kummerRat 4 fermatQuartic) = quarticY from rfl, h0,
    zero_pow (by norm_num)] at h
  have hf : (C 2 - X ^ 4 : ℂ[X]) = 0 := quartic_polynomial_injective (by rw [map_zero]; exact h.symm)
  have := congrArg (eval 0) hf
  simp at this
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- `a + b·x + c·y = 0` in the quartic's function field forces `a = b = c = 0`: the
minimal polynomial of `y` over `ℂ(x)` has degree four. -/
lemma quartic_lin_eq_zero {a b c : ℂ}
    (h : algebraMap ℂ K₄ a + algebraMap ℂ K₄ b * quarticX + algebraMap ℂ K₄ c * quarticY = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  set A : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (C a + C b * X) with hAdef
  set B : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) c with hBdef
  have hmk : AdjoinRoot.mk (kummerRat 4 fermatQuartic) (C A + C B * X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← h]
    rw [hAdef, hBdef, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄,
      ← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) K₄, map_add, map_mul]
    simp only [quarticX, kummerX, quarticY]
    rw [C_eq_algebraMap, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄,
      ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄]
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hdeg : (C A + C B * X).natDegree < (kummerRat 4 fermatQuartic).natDegree := by
    rw [show (kummerRat 4 fermatQuartic).natDegree = 4 from natDegree_X_pow_sub_C]
    have := natDegree_linear_le (a := B) (b := A)
    rw [add_comm] at this
    omega
  have hzero := eq_zero_of_dvd_of_natDegree_lt hmk hdeg
  have hA : A = 0 := by simpa using congrArg (coeff · 0) hzero
  have hB : B = 0 := by simpa using congrArg (coeff · 1) hzero
  have hpoly : (C a + C b * X : ℂ[X]) = 0 :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ) (hA.trans (map_zero _).symm)
  have ha : a = 0 := by simpa using congrArg (coeff · 0) hpoly
  have hb : b = 0 := by simpa using congrArg (coeff · 1) hpoly
  have hc : c = 0 := (algebraMap ℂ (RatFunc ℂ)).injective (hB.trans (map_zero _).symm)
  exact ⟨ha, hb, hc⟩
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution : LinearIndependent ℂ quarticHolo := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∑ i, g i • quarticHolo i =
      ((algebraMap ℂ K₄ (g 0) + algebraMap ℂ K₄ (g 1) * quarticX +
          algebraMap ℂ K₄ (g 2) * quarticY) * quarticY⁻¹ ^ 3) •
        KaehlerDifferential.D ℂ K₄ quarticX := by
    simp only [Fin.sum_univ_three, quarticHolo, quarticHoloNum, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [← algebraMap_smul K₄ (g 0), ← algebraMap_smul K₄ (g 1), ← algebraMap_smul K₄ (g 2),
      smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
    congr 1
    ring
  rw [hsum] at hg
  have hcoef := (smul_eq_zero.mp hg).resolve_right (kummer_D_x_ne_zero 4 fermatQuartic)
  have hlin : algebraMap ℂ K₄ (g 0) + algebraMap ℂ K₄ (g 1) * quarticX +
      algebraMap ℂ K₄ (g 2) * quarticY = 0 :=
    (mul_eq_zero.mp hcoef).resolve_right (pow_ne_zero 3 (inv_ne_zero quarticY_ne_zero))
  obtain ⟨h0, h1, h2⟩ := quartic_lin_eq_zero hlin
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
end

#print axioms solution
