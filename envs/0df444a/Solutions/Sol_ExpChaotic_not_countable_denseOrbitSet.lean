-- Prove2me | solution 1 for ExpChaotic.not_countable_denseOrbitSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:15.1773+00:00
-- url     : https://prove2.me/submissions/934c70fd-17b6-4401-b370-e09526187ab1

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_countable_denseOrbitSet_exp


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution : ¬ denseOrbitSet.Countable := by
  exact ExponentialJuliaSetMisiurewicz.not_countable_denseOrbitSet_exp
end ExpChaotic
