-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_global_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/d9472398-21fd-4a6e-8383-a417d0a8be4e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_toLp
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_tendsto

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ =>
        (normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k))
      atTop (nhds (hh.toLp h)) := by
  simpa only [normalizedCoverMollificationL2_toLp] using
    normalizedCoverMollificationL2_tendsto (hh.toLp h)
end Ehrhart.TorusStrongCoverMollificationDensity
