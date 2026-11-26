-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_succ_of_lt_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:52.872424+00:00
-- url     : https://prove2.me/submissions/ee9e4135-3e64-44fb-830b-28f9e3f964c8

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
    {n k j : ℕ} (hk : k < n) (hj : j < k) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k (j + 1) := by
  have hnk : 0 < n - k := Nat.sub_pos_of_lt hk
  have hfactor : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos _) hnk
  have hcoef : (j + 1) * (n - k) ≤ (n - j) * k := by
    calc
      (j + 1) * (n - k) ≤ k * (n - k) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
      _ ≤ k * (n - j) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hj.le n)
      _ = (n - j) * k := Nat.mul_comm _ _
  apply Nat.le_of_mul_le_mul_right _ hfactor
  calc
    scaledBinomialMass n k j * ((j + 1) * (n - k))
        ≤ scaledBinomialMass n k j * ((n - j) * k) := by
          exact Nat.mul_le_mul_left _ hcoef
    _ = scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k)) := by
          symm
          exact scaledBinomialMass_succ_cross (hj.trans hk)
end CollatzEndpointTransport.FixedTotal
