-- Prove2me | solution 1 for ExpChaotic.devaney_chaotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:20:41.343236+00:00
-- url     : https://prove2.me/submissions/ec1f0d45-092d-4e81-9dbe-14e86c2e3a4b

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_devaney_chaotic_exp


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution : IsDevaneyChaotic Complex.exp := by
  exact ExponentialJuliaSetMisiurewicz.devaney_chaotic_exp
end ExpChaotic
