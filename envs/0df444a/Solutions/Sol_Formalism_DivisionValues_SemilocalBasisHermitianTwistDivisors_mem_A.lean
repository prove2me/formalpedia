-- Prove2me | solution 1 for Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:31.384906+00:00
-- url     : https://prove2.me/submissions/aef0fd19-ce6f-426e-8070-ba2e5925ec49

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ A w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
