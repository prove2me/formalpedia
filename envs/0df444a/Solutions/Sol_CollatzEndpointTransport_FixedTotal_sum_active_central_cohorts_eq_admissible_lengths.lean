-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_active_central_cohorts_eq_admissible_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:58.514547+00:00
-- url     : https://prove2.me/submissions/7dfef329-2e3e-43f4-9bf6-8b1c0032aa9f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_active_central_cohorts_eq_admissible_filter

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (theta eta : ℝ)
    (F : Fin M → ℕ → ℝ) :
    (∑ s ∈ Finset.range (M + 1),
        ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
            (centralLevelCohortSet M s theta eta), F u s) =
      ∑ u : Fin M,
        ∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
          F u s := by
  classical
  simp_rw [active_central_cohorts_eq_admissible_filter,
    admissibleCohortIndices, shellAdmissibleLengthSet, Finset.sum_filter]
  rw [Finset.sum_comm]
end CollatzEndpointTransport.FixedTotal
