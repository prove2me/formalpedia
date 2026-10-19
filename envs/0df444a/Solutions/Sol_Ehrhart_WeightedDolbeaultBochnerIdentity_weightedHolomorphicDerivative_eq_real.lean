-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weightedHolomorphicDerivative_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/310fb4a0-dc57-4326-bb02-8a601e9cda1e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_potential_complex

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
    (ha : ContDiff ℝ 1 a)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedHolomorphicDerivative a F j z =
      (weightedRealDerivative a F (Pi.single j (1 : ℂ)) z -
        Complex.I *
          weightedRealDerivative a F
            (Pi.single j Complex.I) z) / 2 := by
  unfold weightedHolomorphicDerivative weightedRealDerivative
    holomorphicCoordinate
  rw [fderiv_potential_complex ha z (Pi.single j (1 : ℂ)),
    fderiv_potential_complex ha z (Pi.single j Complex.I)]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
