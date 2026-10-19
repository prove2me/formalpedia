-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.twistedAngularAverage_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/a3391444-c7ac-40e0-9941-dade1fa1c109

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_twistedAngularAverage_coordinate_update

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n) :
    twistedAngularAverage F m x =
      twistedAngularAverage F m 0 := by
  classical
  have hreset : ∀ s : Finset (Fin n),
      twistedAngularAverage F m x =
        twistedAngularAverage F m
          (fun i => if i ∈ s then 0 else x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      calc
        twistedAngularAverage F m x =
          twistedAngularAverage F m
            (fun j => if j ∈ s then 0 else x j) := ih
        _ = twistedAngularAverage F m
            (Function.update
              (fun j => if j ∈ s then 0 else x j) i 0) :=
          twistedAngularAverage_coordinate_update
            hF hperiod m _ i 0
        _ = twistedAngularAverage F m
            (fun j => if j ∈ insert i s then 0 else x j) := by
          congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [Function.update, hji]
  calc
    twistedAngularAverage F m x =
        twistedAngularAverage F m
          (fun i => if i ∈ (Finset.univ : Finset (Fin n))
            then 0 else x i) := hreset Finset.univ
    _ = twistedAngularAverage F m 0 := by
      congr 1
      funext i
      simp
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
