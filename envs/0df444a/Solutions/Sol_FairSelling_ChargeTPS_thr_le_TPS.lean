-- Prove2me | solution 1 for FairSelling.ChargeTPS.thr_le_TPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:01.434195+00:00
-- url     : https://prove2.me/submissions/b85e0244-208a-4f28-af1a-353cca93c100

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
    GeneralTPS.thr v p j ≤ TPS n (v j) p := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  unfold GeneralTPS.thr
  have hfrac : (n : ℝ) / (2 * n - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  nlinarith
end FairSelling.ChargeTPS
