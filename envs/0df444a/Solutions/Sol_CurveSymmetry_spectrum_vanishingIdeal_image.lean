-- Prove2me | solution 1 for CurveSymmetry.spectrum_vanishingIdeal_image
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:35.887612+00:00
-- url     : https://prove2.me/submissions/99e469c5-7b8e-4b8b-ac9c-373a45b0a5b2

-- Solution generated from lean/AffineClosure.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (S : Set (Fin 2 → ℂ)) :
    PrimeSpectrum.vanishingIdeal (affineSpectrumPoint '' S) = vanishingIdeal ℂ S := by
  ext P
  rw [PrimeSpectrum.mem_vanishingIdeal, mem_vanishingIdeal_iff]
  constructor
  · intro h v hv
    have he := h (affineSpectrumPoint v) ⟨v, hv, rfl⟩
    change eval v P = 0 at he
    simpa using he
  · intro h q hq
    rcases hq with ⟨v, hv, rfl⟩
    change eval v P = 0
    simpa using h v hv
end

#print axioms solution
