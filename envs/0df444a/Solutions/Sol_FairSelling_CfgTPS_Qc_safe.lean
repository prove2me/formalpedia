-- Prove2me | solution 1 for FairSelling.CfgTPS.Qc_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:56.924926+00:00
-- url     : https://prove2.me/submissions/b3290aeb-2478-4ba4-8da7-e69f0cd7ed44

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_gapMin_le

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
omit [Fintype G] [DecidableEq G]
namespace FairSelling.CfgTPS
theorem _root_.solution {S : Finset G} (h : 0 < Qc w p req k0 S) (m : Fin n) :
    vbarSum (w m) p S + Qc w p req k0 S ≤ req m := by
  have hq : Qc w p req k0 S = gapMin w p req k0 S := by
    unfold Qc at h ⊢
    rcases max_cases (0:ℝ) (gapMin w p req k0 S) with ⟨he, hle⟩ | ⟨he, hle⟩
    · rw [he] at h; exact absurd h (lt_irrefl 0)
    · exact he
  have := gapMin_le w p req k0 S m
  rw [← hq] at this
  linarith
end FairSelling.CfgTPS
