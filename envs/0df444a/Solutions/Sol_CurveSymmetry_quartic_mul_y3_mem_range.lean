-- Prove2me | solution 1 for CurveSymmetry.quartic_mul_y3_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:03:12.351215+00:00
-- url     : https://prove2.me/submissions/fe62d924-767c-4c6f-87fc-afa1f2176406

-- Solution generated from lean/FermatSplit.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_kummer_mem_range_of_forall_local
import Theorems.Thm_CurveSymmetry_kummer_regularAt_ramified
import Theorems.Thm_CurveSymmetry_kummer_regularAt_unramified
import Theorems.Thm_CurveSymmetry_primeValuationSubring_ne_top
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
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma mem_kummerPlace_iff (z : KummerField n f) :
    z ∈ kummerPlace a b hb ↔ z ∈ kummerLocalRing a b hb :=
  Iff.rfl
end Local
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
lemma kummerLocal_const_mem (z : ℂ) :
    algebraMap ℂ (KummerField n f) z ∈ kummerLocalRing a b hb := by
  rw [IsScalarTower.algebraMap_apply ℂ (KummerRing n f) (KummerField n f)]
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
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
/-- **R01c-2b**: the place at a point is a place over `ℂ` in the sense of R01a. -/
lemma kummerPlace_isComplexPlace : IsComplexPlace (kummerPlace a b hb) :=
  ⟨primeValuationSubring_ne_top _ (kummerEval_ker_ne_bot a b hb), kummerLocal_const_mem a b hb⟩
end Local
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution {F : K₄}
    (hF : F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄) :
    ∃ r : KummerRing 4 fermatQuartic, kummerRingMap 4 fermatQuartic r = F * quarticY ^ 3 := by
  refine kummer_mem_range_of_forall_local (n := 4) (f := fermatQuartic) _ fun a b hb => ?_
  have hreg := mem_holomorphicSpace.mp hF _
    (kummerPlace_isComplexPlace (n := 4) (f := fermatQuartic) a b hb)
  by_cases hfa : fermatQuartic.eval a = 0
  · exact (mem_kummerPlace_iff a b hb _).mp
      ((kummer_regularAt_ramified (n := 4) (f := fermatQuartic) a b hb hfa F).mp hreg)
  · have hF' := (mem_kummerPlace_iff a b hb _).mp
      ((kummer_regularAt_unramified (n := 4) (f := fermatQuartic) a b hb hfa F).mp hreg)
    exact mul_mem hF' (pow_mem (kummerLocal_root_mem (n := 4) (f := fermatQuartic) a b hb) 3)
end

#print axioms solution
