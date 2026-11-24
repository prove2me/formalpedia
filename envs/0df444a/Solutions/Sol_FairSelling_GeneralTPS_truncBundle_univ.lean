-- Prove2me | solution 1 for FairSelling.GeneralTPS.truncBundle_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:33.233001+00:00
-- url     : https://prove2.me/submissions/9078d61e-87de-4315-a1a6-850a14ac53af

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_TPS_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.GeneralTPS
theorem _root_.solution (w p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    truncBundle w p (TPS n w p) Finset.univ = (n : ℝ) * TPS n w p := by
  have hfix : truncSum n w p (TPS n w p) = TPS n w p := TPS_truncSum w p hp
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold truncSum at hfix
  unfold truncBundle trunc
  field_simp at hfix
  linarith
end FairSelling.GeneralTPS
