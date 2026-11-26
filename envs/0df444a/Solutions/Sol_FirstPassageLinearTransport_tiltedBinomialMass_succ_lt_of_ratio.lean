-- Prove2me | solution 1 for FirstPassageLinearTransport.tiltedBinomialMass_succ_lt_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:12.295644+00:00
-- url     : https://prove2.me/submissions/f9ba7520-5a73-49a5-9897-3f03e94dd600

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_succ_balance
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k < n)
    (hratio : ((n - k : ℕ) : ℝ) * p <
      ((k + 1 : ℕ) : ℝ) * (1 - p)) :
    tiltedBinomialMass p n (k + 1) < tiltedBinomialMass p n k := by
  have hmass := tiltedBinomialMass_pos hp₀ hp₁ hkn.le
  have hcoef : 0 < ((k + 1 : ℕ) : ℝ) * (1 - p) := by
    exact mul_pos (by positivity) (sub_pos.mpr hp₁)
  have hbalance := tiltedBinomialMass_succ_balance (p := p) hkn
  apply lt_of_mul_lt_mul_left _ hcoef.le
  calc
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) =
      ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k := hbalance
    _ < ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n k := mul_lt_mul_of_pos_right hratio hmass
end FirstPassageLinearTransport
