-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.devaney_chaotic_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:20:06.30083+00:00
-- url     : https://prove2.me/submissions/562d696c-16da-4e05-9178-d4b29d05a68c

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_topologically_transitive_exp
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_periodicPts_exp


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : IsDevaneyChaotic Complex.exp := by
  exact ⟨Complex.continuous_exp, dense_periodicPts_exp, topologically_transitive_exp⟩
end ExponentialJuliaSetMisiurewicz
