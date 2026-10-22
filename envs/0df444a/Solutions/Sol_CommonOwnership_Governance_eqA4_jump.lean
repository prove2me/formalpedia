-- Prove2me | solution 1 for CommonOwnership.Governance.eqA4_jump
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:50.559894+00:00
-- url     : https://prove2.me/submissions/366a9207-c014-4c31-b84d-6e50ee5ae503

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (β ξ γ sp : ℝ) (hξ : 0 < ξ) (hγ : 0 < γ) (Pi_ : ℝ → ℝ) (hPi : Pi_ sp ≠ 0) :
    surplusQ β ξ γ Pi_ sp - surplusQ β ξ γ Pi_ 0 =
      ξ ^ 2 / (2 * γ) * Kfun β ξ γ sp (Pi_ 0) (Pi_ sp) * Pi_ sp := by
  unfold surplusQ nuStar Kfun quadCost
  field_simp
  ring

