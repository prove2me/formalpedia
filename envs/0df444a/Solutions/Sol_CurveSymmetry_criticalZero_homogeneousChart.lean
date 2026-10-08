-- Prove2me | solution 1 for CurveSymmetry.criticalZero_homogeneousChart
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:29.334372+00:00
-- url     : https://prove2.me/submissions/f66bfa2a-724c-4d32-9efa-7fb669fd41cd

-- Solution generated from lean/HomogeneousCharts.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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
open Filter
open scoped Topology
noncomputable def homogeneousRatios (q : HomogeneousPairs) : Fin 2 → ℂ :=
  ![q.1 0 / q.1 1, q.2 0 / q.2 1]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
private lemma pair_normalize (x : Fin 2 → ℂ) (hx : x 1 ≠ 0) :
    x = x 1 • (![x 0 / x 1, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  field_simp
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
theorem solution (F : HomogeneousPairs → ℂ) (d : ℕ)
    (hscale : ∀ (a b : ℂ) (q : HomogeneousPairs),
      F (a • q.1, b • q.2) = a ^ d * b ^ d * F q) (v : Fin 2 → ℂ) :
    CriticalZero F (homogeneousChart v) ↔ CriticalZero (F ∘ homogeneousChart) v := by
  have hchart : Differentiable ℂ homogeneousChart := by
    unfold homogeneousChart
    apply Differentiable.prodMk
    all_goals
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
  have hratio : DifferentiableAt ℂ homogeneousRatios (homogeneousChart v) := by
    unfold homogeneousRatios homogeneousChart
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;>
      fun_prop (disch := norm_num)
  have hback : homogeneousRatios (homogeneousChart v) = v := by
    ext i
    fin_cases i <;> simp [homogeneousRatios, homogeneousChart]
  constructor
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    simpa using hd.comp v (hchart v).hasFDerivAt
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    let A : HomogeneousPairs → ℂ := fun q => q.1 1 ^ d * q.2 1 ^ d
    let H : HomogeneousPairs → ℂ := (F ∘ homogeneousChart) ∘ homogeneousRatios
    have hH : HasFDerivAt H (0 : HomogeneousPairs →L[ℂ] ℂ) (homogeneousChart v) := by
      have hh := hd
      rw [← hback] at hh
      simpa [H] using hh.comp (homogeneousChart v) hratio.hasFDerivAt
    have hA : DifferentiableAt ℂ A (homogeneousChart v) := by
      dsimp [A]
      fun_prop
    have hH0 : H (homogeneousChart v) = 0 := by simpa [H, hback] using hz
    have hprod : HasFDerivAt (fun q => A q * H q)
        (0 : HomogeneousPairs →L[ℂ] ℂ) (homogeneousChart v) := by
      convert hA.hasFDerivAt.mul hH using 1
      all_goals first | rfl | skip
      apply ContinuousLinearMap.ext
      intro w
      change (0 : ℂ) = A (homogeneousChart v) * 0 + H (homogeneousChart v) * _
      rw [hH0]
      ring
    apply hprod.congr_of_eventuallyEq
    have hopen : IsOpen {q : HomogeneousPairs | q.1 1 ≠ 0 ∧ q.2 1 ≠ 0} := by
      apply IsOpen.inter <;> exact isOpen_ne.preimage (by fun_prop)
    have hmem : homogeneousChart v ∈ {q : HomogeneousPairs | q.1 1 ≠ 0 ∧ q.2 1 ≠ 0} := by
      simp [homogeneousChart]
    filter_upwards [hopen.mem_nhds hmem] with q hq
    have he := hscale (q.1 1) (q.2 1) (homogeneousChart (homogeneousRatios q))
    have hx := pair_normalize q.1 hq.1
    have hy := pair_normalize q.2 hq.2
    simpa [A, H, homogeneousChart, homogeneousRatios, ← hx, ← hy] using he
end

#print axioms solution
