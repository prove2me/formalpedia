-- Prove2me | solution 1 for Ehrhart.TorusDeckPeriodization.complexDeckPeriodization_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/d59254de-50d8-4d0a-97ef-4a8a54a45fc6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckPeriodization
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckPeriodization
theorem _root_.solution
    {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℂ)
    (q : Fin n → ℤ) :
    Function.Periodic (complexDeckPeriodization ψ)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  unfold complexDeckPeriodization
  calc
    (∑' d : Fin n → ℤ,
      ψ (z + TorusCharacters.imaginaryShift q +
        TorusCharacters.imaginaryShift d)) =
      ∑' d : Fin n → ℤ,
        ψ (z + TorusCharacters.imaginaryShift (q + d)) := by
      apply tsum_congr
      intro d
      congr 1
      ext i
      simp [TorusCharacters.imaginaryShift,
        Pi.add_apply, Int.cast_add]
      ring
    _ = ∑' d : Fin n → ℤ,
      ψ (z + TorusCharacters.imaginaryShift d) := by
      exact (Equiv.addLeft q).tsum_eq
        (fun d : Fin n → ℤ =>
          ψ (z + TorusCharacters.imaginaryShift d))
end Ehrhart.TorusDeckPeriodization
