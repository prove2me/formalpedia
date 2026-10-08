-- Prove2me | solution 1 for CurveSymmetry.family_diagonal_tangent_direction_counts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:51.487638+00:00
-- url     : https://prove2.me/submissions/22ef1eb2-aef2-4215-b419-dbd703bae5d1

-- Solution generated from lean/BinaryTangentDirections.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma sphereProjectiveEquiv_finite (z : ℂ) :
    sphereProjectiveEquiv (z : Sphere) = Projectivization.mk ℂ ![z, 1] (by simp) := rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma sphereProjectiveEquiv_infinity :
    sphereProjectiveEquiv (∞ : Sphere) = Projectivization.mk ℂ ![1, 0] (by simp) := rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem binaryTangentDirections_mk (m : ℕ) (a b : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ binaryTangentDirections m a b ↔
      a * v 0 ^ m + b * v 1 ^ m = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change a * (Projectivization.mk ℂ v hv).rep 0 ^ m +
    b * (Projectivization.mk ℂ v hv).rep 1 ^ m = 0 ↔ _
  rw [← hu]
  have he : a * (u • v) 0 ^ m + b * (u • v) 1 ^ m =
      (u.val : ℂ) ^ m * (a * v 0 ^ m + b * v 1 ^ m) := by
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  rw [he]
  simp
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem binaryTangentDirections_finite {m : ℕ} {a b : ℂ}
    (ha : a ≠ 0) (z : ℂ) :
    sphereProjectiveEquiv (z : Sphere) ∈ binaryTangentDirections m a b ↔
      z ^ m = -b / a := by
  rw [sphereProjectiveEquiv_finite, binaryTangentDirections_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, mul_one]
  constructor
  · intro h; apply (eq_div_iff ha).mpr; linear_combination h
  · intro h; have he := (eq_div_iff ha).mp h; linear_combination he
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
def binaryTangentRootEquiv {m : ℕ} [NeZero m] (hm : 0 < m) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (w : ℂ) (hw : w ^ m = -b / a) :
    rootsOfUnity m ℂ ≃ binaryTangentDirections m a b := by
  have hw0 : w ≠ 0 := by
    intro h
    have hz : -b / a = 0 := by simpa [h, hm.ne'] using hw.symm
    exact div_ne_zero (neg_ne_zero.mpr hb) ha hz
  apply Equiv.ofBijective (fun u =>
    ⟨sphereProjectiveEquiv (((u.val : ℂ) * w : ℂ) : Sphere),
      (binaryTangentDirections_finite ha _).mpr (by
        rw [mul_pow, (mem_rootsOfUnity' _ _).mp u.property, one_mul, hw])⟩)
  constructor
  · intro u v h
    have he := sphereProjectiveEquiv.injective (congrArg Subtype.val h)
    apply rootsOfUnity.coe_injective
    exact mul_right_cancel₀ hw0 (OnePoint.coe_injective he)
  · intro p
    obtain ⟨q, hq⟩ := sphereProjectiveEquiv.surjective p.val
    cases q using OnePoint.rec with
    | infty =>
      have hp := p.property
      rw [← hq, sphereProjectiveEquiv_infinity, binaryTangentDirections_mk] at hp
      simp [hm.ne', ha] at hp
    | coe z =>
      have hz := (binaryTangentDirections_finite ha z).mp (hq ▸ p.property)
      have hr : (z / w) ^ m = 1 := by
        rw [div_pow, hz, ← hw, div_self (pow_ne_zero _ hw0)]
      refine ⟨rootsOfUnity.mkOfPowEq (z / w) hr, ?_⟩
      apply Subtype.ext
      simpa only [rootsOfUnity.coe_mkOfPowEq, div_mul_cancel₀ _ hw0] using hq
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
/-- Exactly m distinct projective directions; infinity has been checked, not omitted. -/
theorem binaryTangentDirections_card {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (binaryTangentDirections m a b) = m := by
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) hm
  rw [← Nat.card_congr (binaryTangentRootEquiv hm ha hb w hw), Complex.card_rootsOfUnity]
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) :
    Nat.card (binaryTangentDirections m α (star α)) = m ∧
      Nat.card (binaryTangentDirections m 1 1) = m := by
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  exact ⟨binaryTangentDirections_card hm ha0 (star_ne_zero.mpr ha0),
    binaryTangentDirections_card hm one_ne_zero one_ne_zero⟩
end

#print axioms solution
