-- Prove2me | solution 1 for FirstPassageLinearTransport.tiltedBinomialMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:30.099585+00:00
-- url     : https://prove2.me/submissions/5792f420-be34-4f65-855e-a6a9f5e14ede

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k ≤ n) :
    0 < tiltedBinomialMass p n k := by
  have hchoose : 0 < n.choose k := Nat.choose_pos hkn
  unfold tiltedBinomialMass
  exact mul_pos (mul_pos (by exact_mod_cast hchoose) (pow_pos hp₀ _))
    (pow_pos (sub_pos.mpr hp₁) _)
end FirstPassageLinearTransport
