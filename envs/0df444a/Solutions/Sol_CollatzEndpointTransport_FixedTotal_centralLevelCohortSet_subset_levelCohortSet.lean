-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_subset_levelCohortSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:27.497811+00:00
-- url     : https://prove2.me/submissions/87dde37e-cdf8-4d2d-b4ae-0e8495b20f0f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_empty
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_fixed


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {theta eta : ℝ} (u : Fin M) :
    centralLevelCohortSet M s theta eta u ⊆ levelCohortSet M s u := by
  by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
  · rw [centralLevelCohortSet_eq_fixed u hadm]
    exact fun c hc => hc
  · rw [centralLevelCohortSet_eq_empty u hadm]
    exact Finset.empty_subset _
end CollatzEndpointTransport.FixedTotal
