-- Prove2me | solution 1 for CurveSymmetry.family_arc_equivalence_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:50.873976+00:00
-- url     : https://prove2.me/submissions/baa1c818-ce6b-43f1-9cb1-502bd4594be7

-- Solution generated from lean/FamilyParameterArc.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_anti_mobius_equivalence_iff
import Theorems.Thm_CurveSymmetry_family_mobius_equivalence_iff
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
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
theorem arcParameter_norm (θ : ℝ) : ‖arcParameter θ‖ = 1 := by
  simp [arcParameter, Complex.norm_exp]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem arcParameter_im_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < (arcParameter θ).im := by
  simpa [arcParameter, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos] using
    Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem arcParameter_nonreal {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    arcParameter θ ≠ star (arcParameter θ) := by
  intro he
  have hi := congrArg Complex.im he
  have hp := arcParameter_im_pos hθ
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem arcParameter_injective : Set.InjOn arcParameter (Set.Ioo 0 Real.pi) := by
  intro θ hθ φ hφ he
  apply Real.strictAntiOn_cos.injOn ⟨hθ.1.le, hθ.2.le⟩ ⟨hφ.1.le, hφ.2.le⟩
  have hr := congrArg Complex.re he
  simpa [arcParameter, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos] using hr
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem arcParameter_ne_conjugate {θ φ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hφ : φ ∈ Set.Ioo 0 Real.pi) :
    arcParameter φ ≠ star (arcParameter θ) := by
  intro he
  have hi := congrArg Complex.im he
  have hp := arcParameter_im_pos hθ
  have hq := arcParameter_im_pos hφ
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 2 ≤ m) {θ φ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hφ : φ ∈ Set.Ioo 0 Real.pi) :
    ((∃ g : MobiusMatrix, (fun p : Sphere => g • p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ)) ∨
     (∃ g : MobiusMatrix, (fun p : Sphere => g • OnePoint.map (star : ℂ → ℂ) p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ))) ↔ θ = φ := by
  rw [family_mobius_equivalence_iff hm (arcParameter_nonreal hθ)
      (arcParameter_nonreal hφ) (arcParameter_norm θ) (arcParameter_norm φ),
    family_anti_mobius_equivalence_iff hm (arcParameter_nonreal hθ)
      (arcParameter_nonreal hφ) (arcParameter_norm θ) (arcParameter_norm φ)]
  constructor
  · rintro (he | he)
    · exact (arcParameter_injective hφ hθ he).symm
    · exact (arcParameter_ne_conjugate hθ hφ he).elim
  · intro he
    exact Or.inl (congrArg arcParameter he.symm)
end

#print axioms solution
