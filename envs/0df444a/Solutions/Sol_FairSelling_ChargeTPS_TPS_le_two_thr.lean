-- Prove2me | solution 1 for FairSelling.ChargeTPS.TPS_le_two_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:57.607186+00:00
-- url     : https://prove2.me/submissions/f34d8b64-6a14-421a-9ed0-62ddf3032260

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_TPS_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  unfold GeneralTPS.thr
  have hfrac : (1:ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
    rw [show 2 * ((n:ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
      le_div_iff₀ (by linarith)]
    linarith
  nlinarith
end FairSelling.ChargeTPS
