-- Prove2me | solution 1 for FD1D.DyadicMass.allNonneg_ofLeafVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:24.596853+00:00
-- url     : https://prove2.me/submissions/7c0efd93-327c-4e54-bc99-a66798ba8a23

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution (L : ℕ) (f : Fin (2 ^ L) → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (ofLeafVector L f).allNonneg := by
  induction L with
  | zero =>
      simpa [ofLeafVector, allNonneg] using hf 0
  | succ L ih =>
      simp only [ofLeafVector, allNonneg]
      constructor
      · apply ih
        intro i
        exact hf _
      · apply ih
        intro i
        exact hf _
end FD1D.DyadicMass
