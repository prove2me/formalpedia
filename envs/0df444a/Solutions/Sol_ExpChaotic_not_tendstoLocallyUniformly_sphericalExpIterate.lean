-- Prove2me | solution 1 for ExpChaotic.not_tendstoLocallyUniformly_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:15.720174+00:00
-- url     : https://prove2.me/submissions/7139346a-c549-4201-b037-6ac1be5db6c4

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformly_expIterate_comp


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : U → RiemannSphere) :
    ¬ TendstoLocallyUniformly (fun n (z : U) => sphericalExpIterate (φ n) z) g atTop := by
  apply ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformly_expIterate_comp
    (q := fun w : ℂ => (w : RiemannSphere)) OnePoint.continuous_coe _ hU hUne hφ g
  exact fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)
end ExpChaotic
