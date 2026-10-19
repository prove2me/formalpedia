-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.differentiable_coordinateHolomorphicSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/0ff07dda-7f75-4591-ba3c-1ce211c123a3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452
namespace Ehrhart.HolomorphicLaurentFourierCompletenessBridge
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) :
    Differentiable ℂ (coordinateHolomorphicSlice F ζ i) := by
  unfold coordinateHolomorphicSlice
  change Differentiable ℂ
    (F ∘ fun w : ℂ => fun j => if j = i then w else ζ j)
  apply hF.comp
  apply differentiable_pi.mpr
  intro j
  by_cases hji : j = i
  · simp [hji]
  · simp [hji]
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
