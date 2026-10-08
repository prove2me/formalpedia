-- Prove2me | solution 1 for CurveSymmetry.quadRing_isMaximal_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:22.751734+00:00
-- url     : https://prove2.me/submissions/04456e1b-e85a-49bc-8ccf-94a73f4d3916

-- Solution generated from lean/QuadraticRing.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
variable (h : ℂ[X])
lemma quadEval_surjective (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    Function.Surjective (quadEval h c d hd) :=
  fun z => ⟨AdjoinRoot.of _ (C z), by rw [quadEval_of, eval_C]⟩
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X])
theorem solution (𝔪 : Ideal (QuadRing h)) :
    𝔪.IsMaximal ↔ ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), 𝔪 = RingHom.ker (quadEval h c d hd) := by
  constructor
  · intro hmax
    have hcomap := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
      (algebraMap ℂ[X] (QuadRing h)) (fun x => Algebra.IsIntegral.isIntegral x) 𝔪
    obtain ⟨c, hc⟩ := exists_X_sub_C_mem hcomap
    obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (h.eval c) two_pos
    let : Field (QuadRing h ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let q := Ideal.Quotient.mk 𝔪
    let ι := algebraMap ℂ (QuadRing h ⧸ 𝔪)
    have hqX : q (AdjoinRoot.of _ X) = ι c := by
      have hmem : AdjoinRoot.of (quadPoly h) (X - C c) ∈ 𝔪 := hc
      have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, sub_eq_zero] at h0
      rw [h0]
      rfl
    have hqp (p : ℂ[X]) : q (AdjoinRoot.of _ p) = ι (p.eval c) := by
      induction p using Polynomial.induction_on' with
      | add p r hp hr => rw [map_add, map_add, hp, hr, eval_add, map_add]
      | monomial n a =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, hqX, eval_mul,
            eval_C, eval_pow, eval_X, map_mul, map_pow]
          rfl
    have hroot : (q (AdjoinRoot.root _) - ι d₀) * (q (AdjoinRoot.root _) + ι d₀) = 0 := by
      have hsq : AdjoinRoot.root (quadPoly h) ^ 2 = AdjoinRoot.of _ h := by
        have h0 := AdjoinRoot.eval₂_root (quadPoly h)
        rw [eval₂_quadPoly, sub_eq_zero] at h0
        exact h0
      have := congrArg q hsq
      rw [map_pow, hqp, ← hd₀, map_pow] at this
      linear_combination this
    obtain ⟨d, hdd, hqr⟩ : ∃ d : ℂ, d ^ 2 = h.eval c ∧ q (AdjoinRoot.root _) = ι d := by
      rcases mul_eq_zero.mp hroot with h1 | h1
      · exact ⟨d₀, hd₀, sub_eq_zero.mp h1⟩
      · exact ⟨-d₀, by rw [neg_sq, hd₀], by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h1⟩
    refine ⟨c, d, hdd, ?_⟩
    have hext : q = ι.comp (quadEval h c d hdd) := by
      apply AdjoinRoot.ringHom_ext
      · ext p
        · simp only [RingHom.comp_apply]
          rw [hqp, quadEval_of]
        · simp only [RingHom.comp_apply]
          rw [hqp, quadEval_of]
      · simp only [RingHom.comp_apply]
        rw [hqr, quadEval_root]
    have hker := congrArg RingHom.ker hext
    rw [Ideal.mk_ker, RingHom.ker_comp_of_injective _ ι.injective] at hker
    exact hker
  · rintro ⟨c, d, hd, rfl⟩
    exact RingHom.ker_isMaximal_of_surjective _ (quadEval_surjective h c d hd)
end

#print axioms solution
