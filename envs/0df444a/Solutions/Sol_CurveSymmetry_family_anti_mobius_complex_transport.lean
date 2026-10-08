-- Prove2me | solution 1 for CurveSymmetry.family_anti_mobius_complex_transport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:25.598996+00:00
-- url     : https://prove2.me/submissions/7e2dc33b-871b-4d4b-9f06-8ba213180ceb

-- Solution generated from lean/FamilyGlobalTransport.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_mobius_complex_transport
import Theorems.Thm_CurveSymmetry_sphericalFamily_projective_iff
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
open OnePoint
lemma sphereRealDiagonal_conjugate (p : Sphere) :
    sphereRealDiagonal (OnePoint.map (star : ℂ → ℂ) p) = (sphereRealDiagonal p).swap := by
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [sphereRealDiagonal]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma familyBihomogeneous_swap (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α y x = familyBihomogeneous m (star α) x y := by
  simp only [familyBihomogeneous, star_star]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma familyProjective_swap_iff (m : ℕ) (α : ℂ) (p : ProjectiveLine × ProjectiveLine) :
    p.swap ∈ familyProjectiveCurve m α ↔ p ∈ familyProjectiveCurve m (star α) := by
  change familyBihomogeneous m α p.2.rep p.1.rep = 0 ↔ _
  rw [familyBihomogeneous_swap]
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma sphere_conjugation_involutive (p : Sphere) :
    OnePoint.map (star : ℂ → ℂ) (OnePoint.map (star : ℂ → ℂ) p) = p := by
  cases p using OnePoint.rec <;> simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugate_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m (star α) := by
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  rw [← sphericalFamily_projective_iff hm ha, sphereRealDiagonal_conjugate,
    familyProjective_swap_iff, sphericalFamily_projective_iff hm has]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedAntiMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  have hhol : ∀ q ∈ sphericalFamily m (star α), g • q ∈ sphericalFamily m β := by
    intro q hq
    have hconj := (conjugate_mem_sphericalFamily_iff hm ha q).mpr hq
    simpa only [sphere_conjugation_involutive] using hmap (OnePoint.map (star : ℂ → ℂ) q) hconj
  change complexifiedMobius g p.swap ∈ familyProjectiveCurve m β ↔ _
  rw [family_mobius_complex_transport hm has hb g hhol, familyProjective_swap_iff, star_star]
end

#print axioms solution
