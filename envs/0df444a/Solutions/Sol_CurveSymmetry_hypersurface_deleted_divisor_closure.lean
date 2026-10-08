-- Prove2me | solution 1 for CurveSymmetry.hypersurface_deleted_divisor_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:06.989664+00:00
-- url     : https://prove2.me/submissions/a3b169cd-0e85-4398-a0e7-56583615c75c

-- Solution generated from lean/MixedCornerClosure.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private theorem irreducible_factor_in_prime (p : PrimeSpectrum BPoly) (F : BPoly) :
    F ≠ 0 → F ∈ p.asIdeal →
      ∃ q : BPoly, Irreducible q ∧ q ∣ F ∧ q ∈ p.asIdeal := by
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero => intro h; exact (h rfl).elim
  | unit u hu =>
      intro _ hmem
      exact (p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)).elim
  | mul a i ha hi ih =>
      intro _ hmem
      rcases p.isPrime.mem_or_mem hmem with hiI | haI
      · exact ⟨i, hi, dvd_mul_right i a, hiI⟩
      · obtain ⟨q, hq, hqa, hqI⟩ := ih ha haI
        exact ⟨q, hq, dvd_mul_of_dvd_right hqa i, hqI⟩
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (F u : BPoly) (hF0 : F ≠ 0)
    (havoid : ∀ q : BPoly, Irreducible q → q ∣ F → ¬ q ∣ u) :
    closure (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left (PrimeSpectrum.isClosed_zeroLocus _)
  · intro p hp
    have hpF : F ∈ p.asIdeal := hp (Set.mem_singleton F)
    obtain ⟨q, hq, hqF, hqp⟩ := irreducible_factor_in_prime p F hF0 hpF
    let η : PrimeSpectrum BPoly := ⟨Ideal.span {q}, Ideal.isPrime_span_singleton_of_prime hq.prime⟩
    have hη : η ∈ PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | u ∉ p.asIdeal} := by
      constructor
      · intro f hf
        rcases Set.mem_singleton_iff.mp hf with rfl
        exact Ideal.mem_span_singleton.mpr hqF
      · intro hqu
        have hd : q ∣ u := Ideal.mem_span_singleton.mp hqu
        exact havoid q hq hqF hd
    have hpη : p ∈ closure ({η} : Set (PrimeSpectrum BPoly)) := by
      rw [PrimeSpectrum.closure_singleton]
      change Ideal.span {q} ≤ p.asIdeal
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqp)
    exact closure_mono (Set.singleton_subset_iff.mpr hη) hpη
end

#print axioms solution
