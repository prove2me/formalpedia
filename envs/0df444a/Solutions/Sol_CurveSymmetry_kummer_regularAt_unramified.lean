-- Prove2me | solution 1 for CurveSymmetry.kummer_regularAt_unramified
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:36.352973+00:00
-- url     : https://prove2.me/submissions/024799c1-7d3e-4bfc-ad75-f5b9799f7148

-- Solution generated from lean/KummerPlaces.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_mem_regularAt_iff_of_generator
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
section Genus
variable {K : Type*} [Field K] [Algebra ℂ K]
/-- A generator of the differentials of a ring `A` inside `K` gives the generator condition of
`mem_regularAt_iff_of_generator` for the elements of `A`. -/
theorem exists_D_eq_smul_of_span_eq_top {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra A K]
    [IsScalarTower ℂ A K] {u : A}
    (hu : Submodule.span A {KaehlerDifferential.D ℂ A u} = ⊤) (b : A) :
    ∃ g : A, KaehlerDifferential.D ℂ K (algebraMap A K b) =
      algebraMap A K g • KaehlerDifferential.D ℂ K (algebraMap A K u) := by
  have hb : KaehlerDifferential.D ℂ A b ∈ Submodule.span A {KaehlerDifferential.D ℂ A u} := by
    rw [hu]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hb
  refine ⟨g, ?_⟩
  have hmap := congrArg (KaehlerDifferential.map ℂ ℂ A K) hg
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hmap
  rw [← hmap, IsScalarTower.algebraMap_smul]
end Genus
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
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
omit [NeZero n] [Fact (Squarefree f)] [Fact (0 < f.natDegree)] in
/-- Constants of `ℂ` represent every residue of the coordinate ring at the point. -/
theorem kummerRing_residue (s : KummerRing n f) :
    ∃ r : ℂ, s - algebraMap ℂ (KummerRing n f) r ∈ RingHom.ker (kummerEval n f a b hb) := by
  refine ⟨kummerEval n f a b hb s, ?_⟩
  have hconst : kummerEval n f a b hb (algebraMap ℂ (KummerRing n f) (kummerEval n f a b hb s)) =
      kummerEval n f a b hb s := by
    rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (KummerRing n f), kummerEval_algebraMap,
      ← Polynomial.C_eq_algebraMap, eval_C]
  rw [RingHom.mem_ker, map_sub, hconst, sub_self]
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
/-- **R01c-2b**: at a point, the differentials of the local ring are generated by `du` for any
generator `u` of its maximal ideal. -/
theorem kummerLocal_kaehler_span_eq_top {u : kummerLocalRing a b hb}
    (hu : IsLocalRing.maximalIdeal (kummerLocalRing a b hb) = Ideal.span {u}) :
    Submodule.span (kummerLocalRing a b hb)
      {KaehlerDifferential.D ℂ (kummerLocalRing a b hb) u} = ⊤ :=
  localKaehler_span_eq_top
    (localization_residue (RingHom.ker (kummerEval n f a b hb)) (kummerRing_residue a b hb)) hu
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
/-- A generator of the local maximal ideal gives the generator condition of R01a. -/
lemma kummerPlace_generator {u : kummerLocalRing a b hb}
    (hu : IsLocalRing.maximalIdeal (kummerLocalRing a b hb) = Ideal.span {u}) :
    ∀ c ∈ kummerPlace a b hb, ∃ g ∈ kummerPlace a b hb,
      KaehlerDifferential.D ℂ (KummerField n f) c =
        g • KaehlerDifferential.D ℂ (KummerField n f) (u : KummerField n f) := by
  intro c hc
  obtain ⟨g, hg⟩ := exists_D_eq_smul_of_span_eq_top (K := KummerField n f)
    (kummerLocal_kaehler_span_eq_top a b hb hu) ⟨c, hc⟩
  exact ⟨g, g.2, hg⟩
end Local
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
variable (a b : ℂ) (hb : b ^ n = f.eval a)
theorem solution (hfa : f.eval a ≠ 0) (F : KummerField n f) :
    F • KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) ∈ regularAt (kummerPlace a b hb) ↔
      F ∈ kummerPlace a b hb := by
  set u : kummerLocalRing a b hb :=
    algebraMap (KummerRing n f) (kummerLocalRing a b hb) (kummerShift n f a)
  have hu := kummer_unramified_maximalIdeal a b hb (kummerLocalRing a b hb) hfa
  have hDu : KaehlerDifferential.D ℂ (KummerField n f) (u : KummerField n f) =
      KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
    have hcoe : (u : KummerField n f) = kummerX n f - algebraMap ℂ (KummerField n f) a := by
      show algebraMap (KummerRing n f) (KummerField n f) (kummerShift n f a) = _
      rw [kummerShift, ← IsScalarTower.algebraMap_apply ℂ[X] (KummerRing n f) (KummerField n f),
        map_sub, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] (KummerField n f)]
      rfl
    rw [hcoe, map_sub, Derivation.map_algebraMap, sub_zero]
  rw [mem_regularAt_iff_of_generator u.2 (kummerLocal_const_mem a b hb)
    (kummerPlace_generator a b hb hu), hDu]
  constructor
  · rintro ⟨g, hg, hω⟩
    rw [smul_left_injective (KummerField n f) (kummer_D_x_ne_zero n f) hω]
    exact hg
  · intro hF
    exact ⟨F, hF, rfl⟩
end

#print axioms solution
