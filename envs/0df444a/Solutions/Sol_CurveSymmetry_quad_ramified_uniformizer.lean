-- Prove2me | solution 1 for CurveSymmetry.quad_ramified_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:27.706803+00:00
-- url     : https://prove2.me/submissions/31557dba-8830-42f3-add1-91c33e5a4b0b

-- Solution generated from lean/PlaceUniformizers.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
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
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma quadEval_root (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    quadEval h c d hd (AdjoinRoot.root _) = d :=
  AdjoinRoot.lift_root _
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadEval_algebraMap (p : ℂ[X]) :
    quadEval h c d hd (algebraMap ℂ[X] (QuadRing h) p) = p.eval c := by
  rw [AdjoinRoot.algebraMap_eq, quadEval_of]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadRing_root_sq : AdjoinRoot.root (quadPoly h) ^ 2 = algebraMap ℂ[X] (QuadRing h) h := by
  have := AdjoinRoot.eval₂_root (quadPoly h)
  rw [eval₂_quadPoly] at this
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination this
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- At a ramified point place, `t − c` is a multiple of `w` in the local ring. -/
lemma quadShift_mem_span_root (hc : h.eval c = 0) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  have hkmem : algebraMap ℂ[X] (QuadRing h) k ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap]
    exact hkc
  obtain ⟨y, hy⟩ := (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hkmem⟩).exists_right_inv
  have hfactor : quadShift h c * algebraMap ℂ[X] (QuadRing h) k =
      AdjoinRoot.root (quadPoly h) * AdjoinRoot.root (quadPoly h) := by
    rw [quadShift, ← map_mul, ← hk, ← sq, quadRing_root_sq]
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap (QuadRing h) _
    (AdjoinRoot.root (quadPoly h)) * y, ?_⟩
  calc algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)
      = algebraMap (QuadRing h) (quadLocalRing h c d hd)
          (quadShift h c * algebraMap ℂ[X] (QuadRing h) k) * y := by
        rw [map_mul, mul_assoc, hy, mul_one]
    _ = algebraMap (QuadRing h) (quadLocalRing h c d hd) (AdjoinRoot.root (quadPoly h)) *
          (algebraMap (QuadRing h) _ (AdjoinRoot.root (quadPoly h)) * y) := by
        rw [hfactor, map_mul, mul_assoc]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- Every element of the point ideal becomes a multiple of `w` in the local ring, at a
ramified place. -/
lemma quadKer_le_span_root (hc : h.eval c = 0) (p : QuadRing h)
    (hp : p ∈ RingHom.ker (quadEval h c d hd)) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) p ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  have hd0 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd, hc]
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h p
  rw [RingHom.mem_ker, map_add, map_mul, quadEval_algebraMap, quadEval_algebraMap,
    quadEval_root, hd0, mul_zero, add_zero] at hp
  obtain ⟨qa, hqa⟩ := (dvd_iff_isRoot (a := c) (p := a)).mpr hp
  have ha : algebraMap ℂ[X] (QuadRing h) a =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa := by
    rw [quadShift, ← map_mul, ← hqa]
  rw [ha, map_add, map_mul, map_mul]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right _ _ (quadShift_mem_span_root h c d hd hc)
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (hc : h.eval c = 0) :
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) =
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  have hd0 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd, hc]
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (RingHom.ker (quadEval h c d hd)).primeCompl x
    have hmem : a ∈ RingHom.ker (quadEval h c d hd) :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (quadLocalRing h c d hd)
        (RingHom.ker (quadEval h c d hd)) a s).mp hx
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (quadKer_le_span_root h c d hd hc a hmem)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (quadLocalRing h c d hd)
      (RingHom.ker (quadEval h c d hd)) (AdjoinRoot.root (quadPoly h))).mpr ?_
    rw [RingHom.mem_ker, quadEval_root, hd0]
end

#print axioms solution
