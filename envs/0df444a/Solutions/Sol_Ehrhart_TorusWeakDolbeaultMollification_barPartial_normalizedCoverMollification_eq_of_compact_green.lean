-- Prove2me | solution 1 for Ehrhart.TorusWeakDolbeaultMollification.barPartial_normalizedCoverMollification_eq_of_compact_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/9ed3fef8-a44a-4181-b3ec-9a2377891d5e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeakDolbeaultMollification_barPartial_complexReal_convolution_eq_of_compact_green

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakDolbeaultMollification
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths DolbeaultRegularity DolbeaultGraphDistributionBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeakDolbeaultMollification
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {G : Fin n → TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : ∀ (ψ : TorusCharacters.LogSpace n → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ j : Fin n,
        (∫ t : TorusCharacters.LogSpace n,
          g t * coverBarPartialTest ψ j t
          ∂(volume : Measure (TorusCharacters.LogSpace n))) =
        -(2 : ℂ) *
          (∫ t : TorusCharacters.LogSpace n,
            G j t * (ψ t : ℂ)
            ∂(volume : Measure (TorusCharacters.LogSpace n))))
    (k : ℕ) (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate (normalizedCoverMollification g k) x j =
      normalizedCoverMollification (G j) k x := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have h := barPartial_complexReal_convolution_eq_of_compact_green
    (κ := κ) hg hκ hκcompact hweak x j
  simpa only [normalizedCoverMollification, κ,
    complex_convolution_flip] using h
end Ehrhart.TorusWeakDolbeaultMollification
