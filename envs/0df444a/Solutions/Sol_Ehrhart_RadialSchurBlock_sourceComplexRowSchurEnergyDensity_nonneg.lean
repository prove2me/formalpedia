-- Prove2me | solution 1 for Ehrhart.RadialSchurBlock.sourceComplexRowSchurEnergyDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/9bbdd597-dc07-435e-a8ab-3dfabb2069ee

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SchurConvexity_complexSchurEnergyDensity_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialSchurBlock
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic EnvelopeGeneralTorusDescent SchurConvexity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
namespace Ehrhart.RadialSchurBlock
theorem _root_.solution {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) :
    0 ≤ sourceComplexRowSchurEnergyDensity A b :=
  complexSchurEnergyDensity_nonneg hA (star b)
end Ehrhart.RadialSchurBlock
