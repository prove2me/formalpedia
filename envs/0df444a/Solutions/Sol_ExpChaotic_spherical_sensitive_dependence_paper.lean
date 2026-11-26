-- Prove2me | solution 1 for ExpChaotic.spherical_sensitive_dependence_paper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:13.475805+00:00
-- url     : https://prove2.me/submissions/f3aa0a69-83eb-4790-8267-463abea330b2

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_spherical_sensitive_dependence_paper


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → ∃ z ∈ U, ∃ w ∈ U,
      ‖expIterate n z‖ ≤ R ∧ δ ≤ ‖expIterate n z - expIterate n w‖) := by
  exact ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_paper hU hUne hR hδ
end ExpChaotic
