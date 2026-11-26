-- Prove2me | solution 1 for FirstPassageLinearTransport.tiltedBinomialMass_succ_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:25.900143+00:00
-- url     : https://prove2.me/submissions/bb010649-896f-418c-8312-9161a56e657d

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} {n k : ℕ} (hkn : k < n) :
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) =
      ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k := by
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  have hchoose :
      ((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        ((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  unfold tiltedBinomialMass
  calc
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        (((n.choose (k + 1) : ℕ) : ℝ) * p ^ (k + 1) *
          (1 - p) ^ (n - (k + 1))) =
        (((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          p ^ (k + 1) * ((1 - p) ^ (n - (k + 1)) * (1 - p)) := by ring
    _ = (((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) *
          p ^ (k + 1) * ((1 - p) ^ (n - (k + 1)) * (1 - p)) := by rw [hchoose]
    _ = ((n - k : ℕ) : ℝ) * p *
          (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
      rw [pow_succ p k, hsub, pow_succ]
      ring
end FirstPassageLinearTransport
