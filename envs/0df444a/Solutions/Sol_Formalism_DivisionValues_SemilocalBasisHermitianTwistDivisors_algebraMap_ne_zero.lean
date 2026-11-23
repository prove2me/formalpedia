-- Prove2me | solution 1 for Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.algebraMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:30.865058+00:00
-- url     : https://prove2.me/submissions/22530f5a-c499-4e0e-b374-ea4db28a56b7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hcompl_le w hs)
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
