-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:07.961308+00:00
-- url     : https://prove2.me/submissions/9fd4d2f0-6c16-4af5-94a7-e79fa9859174

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (w : HeightOneSpectrum R) (c : R) (hc : c ≠ 0) :
    ∃ s, s ∉ w.asIdeal ∧ ∀ w' : HeightOneSpectrum R, w' ≠ w → ∃ t, t ∉ w'.asIdeal ∧ c ∣ t * s := by
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {c}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJw : ¬ J ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsw⟩ := SetLike.not_le_iff_exists.mp hJw
  refine ⟨s, hsw, fun w' hw' => ?_⟩
  have hpow : ¬ w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {c}) ≤ w'.asIdeal := by
    intro h
    have h1 : w.asIdeal ≤ w'.asIdeal := w'.isPrime.le_of_pow_le h
    exact hw' (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htw⟩ := SetLike.not_le_iff_exists.mp hpow
  refine ⟨t, htw, ?_⟩
  have : t * s ∈ Ideal.span {c} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht hsJ
  exact Ideal.mem_span_singleton.mp this
end Formalism.DivisionValues.GluingInclusion
