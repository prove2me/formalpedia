-- Prove2me | solution 2 for FairSelling.reduction_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:47.403095+00:00
-- url     : https://prove2.me/submissions/949fa35d-5212-4133-9cb8-4d2e583dbae1

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction

set_option autoImplicit true
open FairSelling
namespace FairSelling
theorem _root_.solution (μ : ℝ) (hμ : 0 ≤ μ) (n0 n2 n4 t : ℕ) (ht : t ≤ n2) (Gval : ℝ)
    (hG : ((n0 : ℝ) + n2 + n4) * μ - (n2 : ℝ) * ((2 / 3) * μ) - (n4 : ℝ) * μ
        - 2 * (t : ℝ) * ((2 / 3) * μ) ≤ Gval) :
    ((n0 : ℝ) - t) * μ ≤ Gval := by
  have htn : (t : ℝ) ≤ (n2 : ℝ) := by exact_mod_cast ht
  nlinarith [hμ, htn]
end FairSelling
