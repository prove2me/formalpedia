-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.conjIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.715983+00:00
-- url     : https://prove2.me/submissions/8152377c-6ac2-4f16-8ecf-283ce3abeb38

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    conjIdeal (K := K) w.asIdeal = (conjPl w).asIdeal := by
  show Ideal.span _ = Ideal.map (cO K) w.asIdeal
  unfold Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (RingOfIntegers.ext h).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
end Formalism.DivisionValues.GluingInclusion
