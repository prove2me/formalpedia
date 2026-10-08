-- Prove2me | solution 1 for CurveSymmetry.continuous_invertCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:25.824373+00:00
-- url     : https://prove2.me/submissions/913dfa97-d23a-402d-b261-a85ef4bf5390

-- Solution generated from lean/InversionContinuity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_spectrum_vanishingIdeal_image
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem affineSpectrumPoint_injective : Function.Injective affineSpectrumPoint := by
  intro v w h
  ext i
  have hp : X i - C (v i) ∈ (affineSpectrumPoint v).asIdeal := by
    change eval v (X i - C (v i)) = 0
    simp
  rw [h] at hp
  change eval w (X i - C (v i)) = 0 at hp
  have he : w i - v i = 0 := by simpa using hp
  exact (sub_eq_zero.mp he).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
/-- Evaluation identifies complex points with a topological subspace of the
prime spectrum for the explicitly induced Zariski topology. -/
theorem affineZariski_embedding : Topology.IsEmbedding affineSpectrumPoint :=
  ⟨⟨rfl⟩, affineSpectrumPoint_injective⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
theorem affineZariski_polynomial_nonzero_open (P : BPoly) :
    IsOpen {v : Fin 2 → ℂ | eval v P ≠ 0} := by
  exact (PrimeSpectrum.basicOpen P).isOpen.preimage affineZariski_embedding.continuous
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
theorem affineZariski_polynomial_zero_closed (P : BPoly) :
    IsClosed {v : Fin 2 → ℂ | eval v P = 0} := by
  simpa only [Set.compl_ofPred, not_not] using
    (affineZariski_polynomial_nonzero_open P).isClosed_compl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
/-- The induced topology has precisely the usual algebraic closure operator:
closure is the common zero set of all polynomials vanishing on the set.
Thus no closure claim is hidden in the choice of topology. -/
theorem affineZariski_closure (S : Set (Fin 2 → ℂ)) :
    closure S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} := by
  rw [affineZariski_embedding.closure_eq_preimage_closure_image,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    spectrum_vanishingIdeal_image]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Every polynomial after one-coordinate inversion has a polynomial numerator
and a power of that coordinate as denominator. The equality is asserted only
where the denominator is nonzero; no degree bound is needed here. -/
theorem inversion_clear_denominator (i : Fin 2) (P : BPoly) :
    ∃ n : ℕ, ∃ Q : BPoly, ∀ v : Fin 2 → ℂ, v i ≠ 0 →
      eval v Q = (v i) ^ n * eval (invertCoordinate i v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by intro v _; simp⟩
  | add P R hP hR =>
      obtain ⟨n, Q, hQ⟩ := hP
      obtain ⟨k, S, hS⟩ := hR
      refine ⟨n + k, Q * X i ^ k + S * X i ^ n, ?_⟩
      intro v hv
      simp only [map_add, map_mul, map_pow, eval_X]
      rw [hQ v hv, hS v hv, pow_add]
      ring
  | mul_X P j hP =>
      obtain ⟨n, Q, hQ⟩ := hP
      by_cases hj : j = i
      · subst j
        refine ⟨n + 1, Q, ?_⟩
        intro v hv
        rw [hQ v hv]
        have hi : invertCoordinate i v i = (v i)⁻¹ := by simp [invertCoordinate]
        simp only [map_mul, eval_X, hi, pow_succ]
        field_simp
      · refine ⟨n, Q * X j, ?_⟩
        intro v hv
        simp only [map_mul, eval_X, invertCoordinate, if_neg hj]
        rw [hQ v hv]
        ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- On the inversion domain, inverse images of polynomial zero sets are
polynomial zero sets. This algebraic statement is independent of topology. -/
theorem inversion_zero_set_numerator (i : Fin 2) (P : BPoly) :
    ∃ Q : BPoly, ∀ v : Fin 2 → ℂ, v i ≠ 0 →
      (eval (invertCoordinate i v) P = 0 ↔ eval v Q = 0) := by
  obtain ⟨n, Q, hQ⟩ := inversion_clear_denominator i P
  refine ⟨Q, ?_⟩
  intro v hv
  rw [hQ v hv, mul_eq_zero]
  simp [pow_ne_zero n hv]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_inversionContinuity
theorem solution (i : Fin 2) :
    Continuous (fun v : CoordinateNonzero i => invertCoordinate i v.val) := by
  apply continuous_iff_isClosed.mpr
  intro S hS
  have he : S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} :=
    hS.closure_eq.symm.trans (affineZariski_closure S)
  have hpre : (fun v : CoordinateNonzero i => invertCoordinate i v.val) ⁻¹' S =
      ⋂ P ∈ vanishingIdeal ℂ S,
        {v : CoordinateNonzero i | eval (invertCoordinate i v.val) P = 0} := by
    ext v
    conv_lhs => rw [he]
    simp
  rw [hpre]
  apply isClosed_biInter
  intro P _
  obtain ⟨Q, hQ⟩ := inversion_zero_set_numerator i P
  have hz : {v : CoordinateNonzero i | eval (invertCoordinate i v.val) P = 0} =
      {v : CoordinateNonzero i | eval v.val Q = 0} := by
    ext v
    exact hQ v.val v.property
  rw [hz]
  exact (affineZariski_polynomial_zero_closed Q).preimage continuous_subtype_val
end

#print axioms solution
