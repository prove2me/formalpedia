-- Prove2me | solution 1 for Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:42.388411+00:00
-- url     : https://prove2.me/submissions/57d0ff22-4c52-4214-badb-9a72316e0040

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (h1 : x ∉ w.asIdeal)
    (h2 : x ∉ (conjPl w).asIdeal) : x ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal := by
  apply Submonoid.subset_closure
  refine ⟨h1, fun t ht htw => h2 ?_⟩
  have hct : cO K t = x := by
    apply RingOfIntegers.ext
    change star (t : K) = (x : K)
    have ht' : (t : K) = star (x : K) := ht
    rw [ht', star_star]
  rw [← hct]
  exact Ideal.mem_map_of_mem _ htw
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
