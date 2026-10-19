-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.contDiff_weightedHolomorphicDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/bebd22e8-5985-4377-914f-39bfef2b5700

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
namespace Ehrhart.WeightedDolbeaultBochnerIdentity
theorem _root_.solution {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (j : Fin n) :
    ContDiff ℝ 1 (weightedHolomorphicDerivative a F j) := by
  have hac : ContDiff ℝ 2 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  unfold weightedHolomorphicDerivative
  exact (contDiff_holomorphicCoordinate hF j).sub
    ((hF.of_le (by norm_num)).mul
      (contDiff_holomorphicCoordinate hac j))
end Ehrhart.WeightedDolbeaultBochnerIdentity
