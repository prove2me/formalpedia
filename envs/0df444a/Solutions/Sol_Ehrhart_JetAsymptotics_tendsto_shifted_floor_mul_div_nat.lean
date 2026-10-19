-- Prove2me | solution 1 for Ehrhart.JetAsymptotics.tendsto_shifted_floor_mul_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/fb33e58a-38d7-46f9-868a-aeb6494a2677

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_floor_mul_div_nat

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology
namespace Ehrhart.JetAsymptotics
theorem _root_.solution
    {t : ℝ} (ht : 0 ≤ t) (b : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 t) := by
  have h := (tendsto_floor_mul_div_nat ht).add
    (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
  simpa [Nat.cast_add, add_div] using h
end Ehrhart.JetAsymptotics
