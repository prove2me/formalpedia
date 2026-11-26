-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_countable_denseOrbitSet_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:27.27469+00:00
-- url     : https://prove2.me/submissions/5d51064b-bb4d-4533-9188-270ff8ea68ba

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_ExpChaotic_Periodic
import Definitions.Def_ExpChaotic_Dynamics
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_denseOrbitSet_exp_diff_countable

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : ¬ denseOrbitSetExp.Countable := by
  intro hcount
  obtain ⟨z, hz, hznot⟩ :=
    (dense_denseOrbitSet_exp_diff_countable hcount).nonempty
  exact hznot hz
end ExponentialJuliaSetMisiurewicz
