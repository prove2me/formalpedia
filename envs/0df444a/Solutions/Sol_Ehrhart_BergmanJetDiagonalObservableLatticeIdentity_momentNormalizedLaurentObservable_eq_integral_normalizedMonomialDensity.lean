-- Prove2me | solution 1 for Ehrhart.BergmanJetDiagonalObservableLatticeIdentity.momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/ea16e44f-a0e7-4d8a-99c6-609ed1c440fe

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MonomialIntegrability MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergmanProbabilityEndpoint
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (f : Space n → ℝ)
    (u : monomialIndex K k) :
    momentNormalizedLaurentObservable
        F k f (u : Space n) =
      ∫ x : Space n,
        f x * normalizedMonomialDensity
          K k (momentNormalizedPotential F) u x
        ∂(volume : Measure (Space n)) := by
  unfold momentNormalizedLaurentObservable
    normalizedMonomialDensity monomialNormSquared
  simp_rw [← mul_div_assoc]
  rw [MeasureTheory.integral_div]
end Ehrhart.BergmanJetDiagonalObservableLatticeIdentity
