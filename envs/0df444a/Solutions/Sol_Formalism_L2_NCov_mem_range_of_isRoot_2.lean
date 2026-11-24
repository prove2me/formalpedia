-- Prove2me | solution 2 for Formalism.L2.NCov.mem_range_of_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:49.567461+00:00
-- url     : https://prove2.me/submissions/1b79c2c9-7cf4-489d-ad20-c7c1ffd70bdb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.L2.NCov
theorem _root_.solution (P : (FractionRing O)[X]) (hm : P.Monic)
    (hc : ∀ i, P.coeff i ∈ (algebraMap O (FractionRing O)).range) {μ : FractionRing O} (hμ : P.IsRoot μ) :
    μ ∈ (algebraMap O (FractionRing O)).range := by
  have hlift : P ∈ Polynomial.lifts (algebraMap O (FractionRing O)) :=
    (Polynomial.lifts_iff_coeff_lifts P).mpr (fun n => hc n)
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hm
  have hint : IsIntegral O μ := ⟨Q, hQm, by rw [← Polynomial.eval_map, hQ]; exact hμ⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy⟩
end Formalism.L2.NCov
