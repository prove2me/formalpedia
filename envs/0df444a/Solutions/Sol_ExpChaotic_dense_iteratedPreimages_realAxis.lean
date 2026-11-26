-- Prove2me | solution 1 for ExpChaotic.dense_iteratedPreimages_realAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:58.650113+00:00
-- url     : https://prove2.me/submissions/9f6cec53-85f9-43e7-9b1b-71fcd5dac253

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Definitions.Def_ExpChaotic_Normality
import Definitions.Def_ExpChaotic_PaperConsequences
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Results
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_iterated_preimages_real_axis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution :
    Dense {z : ℂ | ∃ n : ℕ, (expIterate n z).im = 0} := by
  simpa [ExponentialJuliaSetMisiurewicz.OnRealAxis] using
    ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_real_axis
end ExpChaotic
