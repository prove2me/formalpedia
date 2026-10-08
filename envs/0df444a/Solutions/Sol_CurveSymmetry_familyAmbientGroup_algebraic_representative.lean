-- Prove2me | solution 1 for CurveSymmetry.familyAmbientGroup_algebraic_representative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:48.313648+00:00
-- url     : https://prove2.me/submissions/5a326623-4ffb-4fb1-9362-addd75644039

-- Solution generated from lean/FamilyAlgebraic.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_mobius_self_filter
import Theorems.Thm_CurveSymmetry_mobius_antidiagonal_action
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_finite_formula (g : MobiusMatrix) (z : ℂ) :
    g • (z : Sphere) = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_infinity_formula (g : MobiusMatrix) :
    g • (∞ : Sphere) = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma mobius_diagonal_action (g : MobiusMatrix) (hb : g 0 1 = 0) (hc : g 1 0 = 0) :
    g 0 0 / g 1 1 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereDilation (g 0 0 / g 1 1) p := by
  have hn := g.det_ne_zero
  simp only [Matrix.det_fin_two, hb, hc, zero_mul, sub_zero, ne_eq, mul_eq_zero, not_or] at hn
  refine ⟨div_ne_zero hn.1 hn.2, ?_⟩
  intro p
  cases p using OnePoint.rec with
  | infty => simp [mobius_infinity_formula, hc, sphereDilation]
  | coe z =>
    simp [mobius_finite_formula, hb, hc, hn.2, sphereDilation, div_eq_mul_inv,
      mul_comm, mul_assoc]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem mem_familyAmbientGroup_iff (m : ℕ) (α : ℂ) (f : Equiv.Perm Sphere) :
    f ∈ familyAmbientGroup m α ↔
      (∃ g : MobiusMatrix, ∀ p : Sphere, g • p = f p) ∧
        ∀ p, f p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, fun p => congrArg (fun k : Equiv.Perm Sphere => k p) hg⟩, hf⟩
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, Equiv.ext hg⟩, hf⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- The root conditions imply algebraicity over Q, not just over C. -/
theorem family_root_coefficient_algebraic {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : IsAlgebraic ℚ α)
    (hc : c ^ (2 * m) = 1 ∨ c ^ (2 * m) = star α ^ 2) :
    IsAlgebraic ℚ c := by
  apply IsAlgebraic.of_pow (by omega : 0 < 2 * m)
  rcases hc with hc | hc
  · rw [hc]
    exact isAlgebraic_one
  · rw [hc]
    have hs : IsIntegral ℚ (star α) :=
      hα.isIntegral.map (Complex.conjAe.restrictScalars ℚ).toAlgHom
    exact (hs.pow 2).isAlgebraic
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- Every ambient self-map has an algebraic normal-form coefficient when
the normalized family parameter is algebraic. -/
theorem family_mobius_algebraic_forms {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (g : MobiusMatrix)
    (hg : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) :
    ∃ c : ℂ, c ≠ 0 ∧ IsAlgebraic ℚ c ∧
      ((c ^ (2 * m) = 1 ∧ ∀ p : Sphere, g • p = sphereDilation c p) ∨
       (c ^ (2 * m) = star α ^ 2 ∧ ∀ p : Sphere, g • p = sphereInversion c p)) := by
  obtain ⟨c, hc, h⟩ := (family_mobius_self_filter hm ha hα g).mp hg
  refine ⟨c, hc, family_root_coefficient_algebraic (m := m) (by omega) halg ?_, h⟩
  exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- Algebraic coefficients means existence of a GL(2,C) representative with
algebraic entries. An arbitrary scalar rescaling need not have that property. -/
theorem family_mobius_algebraic_representative {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (g : MobiusMatrix)
    (hg : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) :
    ∃ h : MobiusMatrix, (∀ i j, IsAlgebraic ℚ (h i j)) ∧
      ∀ p : Sphere, h • p = g • p := by
  obtain ⟨c, hc, hca, ⟨hr, he⟩ | ⟨hr, he⟩⟩ :=
    family_mobius_algebraic_forms hm ha hα halg g hg
  · let h : MobiusMatrix := Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1]
      (by simpa [Matrix.det_fin_two] using hc)
    refine ⟨h, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        first | exact hca | exact isAlgebraic_zero | exact isAlgebraic_one
    · intro p
      rw [he]
      simpa [h, Matrix.GeneralLinearGroup.mkOfDetNeZero] using
        (mobius_diagonal_action h rfl rfl).2 p
  · let h : MobiusMatrix := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, c; 1, 0]
      (by simpa [Matrix.det_fin_two] using hc)
    refine ⟨h, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        first | exact hca | exact isAlgebraic_zero | exact isAlgebraic_one
    · intro p
      rw [he]
      simpa [h, Matrix.GeneralLinearGroup.mkOfDetNeZero] using
        (mobius_antidiagonal_action h rfl rfl).2 p
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 2 ≤ m)
    {α : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (f : familyAmbientGroup m α) :
    ∃ h : MobiusMatrix, (∀ i j, IsAlgebraic ℚ (h i j)) ∧
      ∀ p : Sphere, h • p = f.val p := by
  obtain ⟨⟨g, hg⟩, hf⟩ := (mem_familyAmbientGroup_iff m α f.val).mp f.property
  obtain ⟨h, hh, he⟩ := family_mobius_algebraic_representative hm ha hα halg g
    (fun p hp => by rw [hg]; exact (hf p).mpr hp)
  exact ⟨h, hh, fun p => (he p).trans (hg p)⟩
end

#print axioms solution
