-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.periodic_coordinateHolomorphicSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/f3e19095-17e4-4fa4-b4d9-01aca955920a

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
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) :
    Function.Periodic (coordinateHolomorphicSlice F ζ i)
      logarithmicPeriod := by
  intro w
  change
    F (fun j => if j = i then w + logarithmicPeriod else ζ j) =
      F (fun j => if j = i then w else ζ j)
  have hshift :
      (fun j : Fin n =>
        if j = i then w + logarithmicPeriod else ζ j) =
        (fun j : Fin n => if j = i then w else ζ j) +
          TorusCharacters.imaginaryShift
            (Pi.single i (1 : ℤ)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [TorusCharacters.imaginaryShift,
        logarithmicPeriod]
    · simp [hji, TorusCharacters.imaginaryShift]
  rw [hshift]
  exact hperiod (Pi.single i (1 : ℤ)) _
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
