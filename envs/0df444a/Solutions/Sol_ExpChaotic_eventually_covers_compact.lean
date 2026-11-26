-- Prove2me | solution 1 for ExpChaotic.eventually_covers_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:06.538355+00:00
-- url     : https://prove2.me/submissions/9c32722c-06a6-4946-be28-b359c84fb654

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact


set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section
namespace ExpChaotic
theorem _root_.solution
    {U K : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → K ⊆ expIterate n '' U) := by
  exact ExponentialJuliaSetMisiurewicz.eventually_covers_compact hU hUne hK hK0
end ExpChaotic
