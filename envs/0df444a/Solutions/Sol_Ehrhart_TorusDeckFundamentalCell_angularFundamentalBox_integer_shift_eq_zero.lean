-- Prove2me | solution 1 for Ehrhart.TorusDeckFundamentalCell.angularFundamentalBox_integer_shift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/6bd72cdc-bbb0-41fa-8780-4b5b30f2a1cc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckFundamentalCell
open Set Function Filter MeasureTheory Matrix
open WeightedTorusDistributionBridge TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckFundamentalCell
theorem _root_.solution
    {n : ℕ} {b t : Space n}
    (ht : t ∈ angularFundamentalBox b)
    {q : Fin n → ℤ}
    (hq : (fun i : Fin n => t i + (q i : ℝ)) ∈
      angularFundamentalBox b) :
    q = 0 := by
  funext i
  have hti := ht i
  have hqi := hq i
  change b i < t i ∧ t i ≤ b i + 1 at hti
  change b i < t i + (q i : ℝ) ∧
    t i + (q i : ℝ) ≤ b i + 1 at hqi
  have hlow : (-1 : ℝ) < (q i : ℝ) := by
    linarith
  have hupp : (q i : ℝ) < 1 := by
    linarith
  have hlowz : (-1 : ℤ) < q i := by
    exact_mod_cast hlow
  have huppz : q i < (1 : ℤ) := by
    exact_mod_cast hupp
  have hz : q i = 0 := by
    omega
  simpa using hz
end Ehrhart.TorusDeckFundamentalCell
