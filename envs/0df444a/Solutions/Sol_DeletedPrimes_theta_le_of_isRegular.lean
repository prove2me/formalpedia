-- Prove2me | solution 1 for DeletedPrimes.theta_le_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:05.71384+00:00
-- url     : https://prove2.me/submissions/57ead3fe-c655-4072-87c6-dcfd6bf4b8e8

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta_set_bddBelow

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsRegular S θ) : theta S ≤ θ :=
  csInf_le (theta_set_bddBelow S) ⟨h0, h⟩
end DeletedPrimes
