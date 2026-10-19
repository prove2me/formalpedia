-- Prove2me | solution 1 for Ehrhart.JetCounting.finrank_le_kernel_add_jetCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/bb5bf99b-0d5c-40be-b404-115cb41f3ced

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetCounting_card_jetIndexLT

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetCounting
open scoped BigOperators
namespace Ehrhart.JetCounting
theorem _root_.solution
    (𝕜 V : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V]
    (n j : ℕ) (hj : 0 < j)
    (jet : V →ₗ[𝕜] (JetIndexLT n j → 𝕜)) :
    Module.finrank 𝕜 V ≤
      Module.finrank 𝕜 (LinearMap.ker jet) + (n + j - 1).choose n := by
  have hrange : Module.finrank 𝕜 (LinearMap.range jet) ≤
      (n + j - 1).choose n := by
    calc
      Module.finrank 𝕜 (LinearMap.range jet) ≤
          Module.finrank 𝕜 (JetIndexLT n j → 𝕜) := Submodule.finrank_le _
      _ = (n + j - 1).choose n := by
        rw [Module.finrank_fintype_fun_eq_card, card_jetIndexLT n j hj]
  have hdimension := LinearMap.finrank_range_add_finrank_ker jet
  omega
end Ehrhart.JetCounting
