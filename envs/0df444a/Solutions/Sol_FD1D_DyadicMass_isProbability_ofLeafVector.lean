-- Prove2me | solution 1 for FD1D.DyadicMass.isProbability_ofLeafVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:38.209807+00:00
-- url     : https://prove2.me/submissions/741fa416-4f0e-4e51-b382-2bcc83ca16e3

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_allNonneg_ofLeafVector
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
    (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = 1) :
    (ofLeafVector L f).IsProbability where
  nonneg := allNonneg_ofLeafVector L f hf
  total_eq_one := by simpa using hsum
end FD1D.DyadicMass
