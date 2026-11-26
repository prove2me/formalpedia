-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulus_tails_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:02.502807+00:00
-- url     : https://prove2.me/submissions/430c234d-6025-4dfb-b893-d78cc11a4234

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H j : ℕ} (hH : 0 < H) (hj : 0 < j) :
    Disjoint
      (Finset.Ico 0 (binomialAnnulusCutoff H j + 1))
      (Finset.Ico (H - binomialAnnulusCutoff H j) (H + 1)) := by
  rw [Finset.disjoint_left]
  intro k hkl hku
  have hW : 3 ≤ binomialAnnulusWidth H := by
    unfold binomialAnnulusWidth
    omega
  have hWle : binomialAnnulusWidth H ≤
      j * binomialAnnulusWidth H := by
    simpa using Nat.mul_le_mul_right (binomialAnnulusWidth H)
      (Nat.succ_le_iff.mpr hj)
  have hd3 : 3 ≤ j * binomialAnnulusWidth H := hW.trans hWle
  have hKlt : binomialAnnulusCutoff H j <
      H - binomialAnnulusCutoff H j := by
    by_cases hd : j * binomialAnnulusWidth H ≤ H / 2 + 1
    · have hsum : binomialAnnulusCutoff H j +
          j * binomialAnnulusWidth H = H / 2 + 1 := by
        exact Nat.sub_add_cancel hd
      have htwoc : 2 * (H / 2) ≤ H := by
        simpa [mul_comm] using Nat.div_mul_le_self H 2
      have htwok : 2 * binomialAnnulusCutoff H j < H := by omega
      have hKleH : binomialAnnulusCutoff H j ≤ H := by omega
      have hcancel := Nat.sub_add_cancel hKleH
      omega
    · have hKzero : binomialAnnulusCutoff H j = 0 := by
        exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hd)
      simp [hKzero, hH]
  have hl := Finset.mem_Ico.mp hkl
  have hu := Finset.mem_Ico.mp hku
  omega
end CollatzEndpointTransport.FixedTotal
