-- Prove2me | solution 1 for ExpChaotic.not_equicontinuousAt_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:07.992363+00:00
-- url     : https://prove2.me/submissions/4a092e2c-cb00-4f2e-b565-4fc4c329ceac

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_sphericalExpIterate


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution (z : ℂ) :
    ¬ EquicontinuousAt sphericalExpIterate z := by
  exact ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_sphericalExpIterate z
end ExpChaotic
