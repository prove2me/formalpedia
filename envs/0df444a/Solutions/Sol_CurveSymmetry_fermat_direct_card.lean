-- Prove2me | solution 1 for CurveSymmetry.fermat_direct_card
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:34.851168+00:00
-- url     : https://prove2.me/submissions/86b8146d-faf5-4250-9f26-bae1e68a3053

-- Solution generated from lean/Sharpness.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_direct_bound_with_opposite
import Theorems.Thm_CurveSymmetry_direct_euclidean_bound
import Theorems.Thm_CurveSymmetry_fermat_degree
import Theorems.Thm_CurveSymmetry_fermat_not_circle
import Theorems.Thm_CurveSymmetry_fermat_realLocus_infinite
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
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
lemma eval_fermat (d : ℕ) (z : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (fermatPolynomial d) =
      z ^ d + star (z ^ d) - 2 := by
  simp [fermatPolynomial, star_pow]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma fermat_root_symmetry {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hroot : ζ ^ d = 1) :
    DirectSymmetry (realLocus (fermatPolynomial d)) ζ 0 := by
  have hn : ‖ζ‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hd.ne').mp
    simpa using congrArg norm hroot
  refine ⟨hn, ?_⟩
  intro z
  simp only [add_zero]
  change MvPolynomial.eval _ (fermatPolynomial d) = 0 ↔ MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, eval_fermat, mul_pow, hroot, one_mul]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma fermat_conjugation (d : ℕ) : OppositeSymmetry (realLocus (fermatPolynomial d)) 1 0 := by
  refine ⟨by simp, ?_⟩
  intro z
  simp only [one_mul, add_zero]
  change MvPolynomial.eval _ (fermatPolynomial d) = 0 ↔ MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, eval_fermat]
  simp [add_comm]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (DirectSymmetries (fermatPolynomial d)) = d := by
  have hd' : 0 < d := by omega
  have hirr := fermat_irreducible hd'
  have hinf := fermat_realLocus_infinite hd'
  have hdeg : 2 ≤ (fermatPolynomial d).totalDegree := by rwa [fermat_degree hd']
  have hnc := fermat_not_circle hd'
  let := (direct_euclidean_bound hirr hdeg hinf hnc).1
  let : NeZero d := ⟨hd'.ne'⟩
  let f : rootsOfUnity d ℂ → DirectSymmetries (fermatPolynomial d) := fun u =>
    ⟨((u.val : ℂ), 0), fermat_root_symmetry hd' ((mem_rootsOfUnity' _ _).mp u.prop)⟩
  have hi : Function.Injective f := by
    intro u v h
    exact rootsOfUnity.coe_injective (congrArg (fun w => w.val.1) h)
  have hlo := Nat.card_le_card_of_injective f hi
  rw [Complex.card_rootsOfUnity] at hlo
  have hhi := direct_bound_with_opposite hirr hdeg hinf hnc ⟨(1, 0), fermat_conjugation d⟩
  rw [fermat_degree hd'] at hhi
  omega
end

#print axioms solution
