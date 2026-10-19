-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_toLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/ffe92220-3b45-4bf9-a849-7fae732369c2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_congr_ae

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
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    normalizedCoverMollificationL2 k (hg.toLp g) =
      (normalizedCoverMollification_memLp hg k).toLp
        (normalizedCoverMollification g k) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(normalizedCoverMollification_memLp
      (MeasureTheory.Lp.memLp (hg.toLp g)) k).coeFn_toLp,
     (normalizedCoverMollification_memLp hg k).coeFn_toLp]
    with x hleft hright
  change
    ((normalizedCoverMollification_memLp
      (MeasureTheory.Lp.memLp (hg.toLp g)) k).toLp
        (normalizedCoverMollification
          (fun y : LogSpace n => (hg.toLp g) y) k)) x = _
  rw [hleft, hright]
  exact congrFun
    (normalizedCoverMollification_congr_ae hg.coeFn_toLp k) x
end Ehrhart.TorusStrongCoverMollificationDensity
