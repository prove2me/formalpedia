-- Prove2me | solution 1 for ExpChaotic.not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:18.043799+00:00
-- url     : https://prove2.me/submissions/f7f3f86a-0da3-4270-9701-9f7c02c27a88

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_sphericalExpIterate


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → RiemannSphere) :
    ¬ TendstoLocallyUniformlyOn (fun n => sphericalExpIterate (φ n)) g atTop U := by
  exact ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_sphericalExpIterate
    hU hUne hφ g
end ExpChaotic
