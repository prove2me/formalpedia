-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.scaledBinomialMass_succ_le_of_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:03.74095+00:00
-- url     : https://prove2.me/submissions/5b21147f-628a-44fc-88b4-fcb2f29624fe

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_succ_cross

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k j : ℕ} (hjn : j < n) (hkj : k ≤ j) :
    scaledBinomialMass n k (j + 1) ≤ scaledBinomialMass n k j := by
  have hkn : k < n := lt_of_le_of_lt hkj hjn
  have hnk : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hfactor : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos _) hnk
  have hcoef : (n - j) * k ≤ (j + 1) * (n - k) := by
    calc
      (n - j) * k ≤ (n - k) * k :=
        Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hkj n)
      _ ≤ (n - k) * (j + 1) :=
        Nat.mul_le_mul_left _ (hkj.trans (Nat.le_succ j))
      _ = (j + 1) * (n - k) := Nat.mul_comm _ _
  apply Nat.le_of_mul_le_mul_right _ hfactor
  calc
    scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k))
        = scaledBinomialMass n k j * ((n - j) * k) :=
          scaledBinomialMass_succ_cross hjn
    _ ≤ scaledBinomialMass n k j * ((j + 1) * (n - k)) := by
          exact Nat.mul_le_mul_left _ hcoef
end CollatzEndpointTransport.FixedTotal
