-- Prove2me | solution 1 for Ehrhart.JetAsymptotics.tendsto_floor_mul_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/f0d2dec4-d16b-4bec-9b0e-3e21b7e753bd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun k : ℕ => (Nat.floor (t * (k : ℝ)) : ℝ) / (k : ℝ))
      atTop (𝓝 t) := by
  refine Filter.Tendsto.congr' ?_
    ((tendsto_nat_floor_mul_div_atTop ht).comp
      tendsto_natCast_atTop_atTop)
  exact Filter.Eventually.of_forall fun _ => rfl
end Ehrhart.JetAsymptotics
