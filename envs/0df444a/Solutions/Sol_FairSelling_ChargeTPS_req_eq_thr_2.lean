-- Prove2me | solution 2 for FairSelling.ChargeTPS.req_eq_thr
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:24:54.958803+00:00
-- url     : https://prove2.me/submissions/ba9260ba-9fbf-4bb4-b11c-4f7d77c63728

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [DecidableEq G]


theorem solution {s : CStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by
  simp [CStage.req,hj]
