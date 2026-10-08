-- Prove2me | solution 1 for CurveSymmetry.quad_unramified_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:29.182864+00:00
-- url     : https://prove2.me/submissions/beea051d-177d-466b-a0ff-3a306260459a

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
lemma quadShift_mem_ker : quadShift h c ∈ RingHom.ker (quadEval h c d hd) := by
  rw [RingHom.mem_ker, quadShift, quadEval_algebraMap]
  simp
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
/-- In the local ring at `(c, d)`, the image of `w − d` is a multiple of `t − c`,
provided `d ≠ 0`. -/
lemma quadRoot_sub_mem_span (hdne : d ≠ 0) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  obtain ⟨q, hq⟩ : (X - C c) ∣ h - C (h.eval c) := X_sub_C_dvd_sub_C_eval
  have hsum : AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d) ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, map_add, quadEval_root, quadEval_algebraMap, eval_C]
    intro hzero
    exact hdne (by linear_combination hzero / 2)
  obtain ⟨y, hy⟩ := (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hsum⟩).exists_right_inv
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap (QuadRing h) _
    (algebraMap ℂ[X] (QuadRing h) q) * y, ?_⟩
  have hfactor : (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) *
      (AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d)) =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) q := by
    have hroot := quadRing_root_sq h
    have hdC : algebraMap ℂ[X] (QuadRing h) (C d) ^ 2 =
        algebraMap ℂ[X] (QuadRing h) (C (h.eval c)) := by
      rw [← map_pow, ← C_pow, hd]
    rw [quadShift, ← map_mul, ← hq, map_sub]
    linear_combination hroot - hdC
  calc algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d))
      = algebraMap (QuadRing h) (quadLocalRing h c d hd)
          ((AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) *
            (AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d))) * y := by
        rw [map_mul, mul_assoc, hy, mul_one]
    _ = algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) *
          (algebraMap (QuadRing h) _ (algebraMap ℂ[X] (QuadRing h) q) * y) := by
        rw [hfactor, map_mul, mul_assoc]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- Every element of the point ideal becomes a multiple of `t − c` in the local ring,
when `d ≠ 0`. -/
lemma quadKer_le_span (hdne : d ≠ 0) (p : QuadRing h)
    (hp : p ∈ RingHom.ker (quadEval h c d hd)) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) p ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h p
  rw [RingHom.mem_ker, map_add, map_mul, quadEval_algebraMap, quadEval_algebraMap,
    quadEval_root] at hp
  obtain ⟨qa, hqa⟩ : (X - C c) ∣ a - C (a.eval c) := X_sub_C_dvd_sub_C_eval
  obtain ⟨qb, hqb⟩ : (X - C c) ∣ b - C (b.eval c) := X_sub_C_dvd_sub_C_eval
  have ha : algebraMap ℂ[X] (QuadRing h) a =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa +
        algebraMap ℂ[X] (QuadRing h) (C (a.eval c)) := by
    rw [quadShift, ← map_mul, ← map_add, ← hqa]
    ring_nf
  have hb : algebraMap ℂ[X] (QuadRing h) b =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qb +
        algebraMap ℂ[X] (QuadRing h) (C (b.eval c)) := by
    rw [quadShift, ← map_mul, ← map_add, ← hqb]
    ring_nf
  have hzero : algebraMap ℂ[X] (QuadRing h) (C (a.eval c)) +
      algebraMap ℂ[X] (QuadRing h) (C (b.eval c)) *
        algebraMap ℂ[X] (QuadRing h) (C d) = 0 := by
    rw [← map_mul, ← map_add, ← C_mul, ← C_add, hp]
    simp
  have hsplit : algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h) =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa +
        algebraMap ℂ[X] (QuadRing h) b *
          (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) +
        algebraMap ℂ[X] (QuadRing h) (C d) *
          (quadShift h c * algebraMap ℂ[X] (QuadRing h) qb) := by
    linear_combination ha + algebraMap ℂ[X] (QuadRing h) (C d) * hb + hzero
  simp only [hsplit, map_add, map_mul]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.mul_mem_left _ _ (quadRoot_sub_mem_span h c d hd hdne)
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (hc : h.eval c ≠ 0) :
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) =
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  have hdne : d ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact hc (by linear_combination -hd)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (RingHom.ker (quadEval h c d hd)).primeCompl x
    have hmem : a ∈ RingHom.ker (quadEval h c d hd) :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (quadLocalRing h c d hd)
        (RingHom.ker (quadEval h c d hd)) a s).mp hx
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (quadKer_le_span h c d hd hdne a hmem)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (quadLocalRing h c d hd)
      (RingHom.ker (quadEval h c d hd)) (quadShift h c)).mpr (quadShift_mem_ker h c d hd)
end

#print axioms solution
