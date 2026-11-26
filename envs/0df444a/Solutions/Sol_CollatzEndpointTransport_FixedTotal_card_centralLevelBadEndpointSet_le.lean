-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_centralLevelBadEndpointSet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:44.177091+00:00
-- url     : https://prove2.me/submissions/488a8dd1-370e-4371-a91b-2102b6be0b54

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadEndpointSet_subset_actual
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_actualLevelBadEndpointSet_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta : ℝ) :
    ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ≤
      C * (3 ^ (s + 1) : ℝ) ^ (1 - D) := by
  have hcard :
      (centralLevelBadEndpointSet S M s theta eta).card ≤
        (actualLevelBadEndpointSet S M s).card :=
    Finset.card_le_card
      (centralLevelBadEndpointSet_subset_actual S M s theta eta)
  have hcardR :
      ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ≤
        ((actualLevelBadEndpointSet S M s).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (card_actualLevelBadEndpointSet_le hS M s)
end CollatzEndpointTransport.FixedTotal
