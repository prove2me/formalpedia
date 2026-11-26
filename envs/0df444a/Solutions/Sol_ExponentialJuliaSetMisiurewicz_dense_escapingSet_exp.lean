-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_escapingSet_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:36.588211+00:00
-- url     : https://prove2.me/submissions/d1cb2d22-2c02-4b4b-811c-7eda819d36fd

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_escapesToInfinity_of_eventually_onRealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_iterated_preimages_real_axis


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : Dense escapingSetExp := by
  apply dense_iterated_preimages_real_axis.mono
  rintro z ⟨m, hm⟩
  exact escapesToInfinity_of_eventually_onRealAxis hm
end ExponentialJuliaSetMisiurewicz
