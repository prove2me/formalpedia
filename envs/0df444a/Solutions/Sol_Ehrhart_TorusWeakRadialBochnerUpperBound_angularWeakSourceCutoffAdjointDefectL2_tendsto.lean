-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialBochnerUpperBound.angularWeakSourceCutoffAdjointDefectL2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/db040aec-1fdd-426c-bf4b-7f4925556cd2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularSourceRadialCutoff_smul_L2_tendsto
import Theorems.Thm_Ehrhart_TorusWeakRadialCutoffCommutator_angularWeakSourceCutoffAdjointCommutator_L2_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakRadialBochnerUpperBound
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreDensity TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology
namespace Ehrhart.TorusWeakRadialBochnerUpperBound
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (d : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C) :
    Tendsto
      (fun m : ℕ => angularWeakSourceCutoffAdjointDefectL2 d W hC m)
      atTop (nhds (-d)) := by
  have hcut :
      Tendsto
        (fun m : ℕ =>
          (angularSourceRadialCutoff_smul_memLp
            (MeasureTheory.Lp.memLp d) m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) • d q))
        atTop (nhds d) := by
    simpa only [MeasureTheory.Lp.toLp_coeFn] using
      (angularSourceRadialCutoff_smul_L2_tendsto
        (MeasureTheory.Lp.memLp d))
  have hcomm :=
    angularWeakSourceCutoffAdjointCommutator_L2_tendsto_zero
      W hC₀ hC
  simpa [angularWeakSourceCutoffAdjointDefectL2] using
    hcut.neg.add hcomm
end Ehrhart.TorusWeakRadialBochnerUpperBound
