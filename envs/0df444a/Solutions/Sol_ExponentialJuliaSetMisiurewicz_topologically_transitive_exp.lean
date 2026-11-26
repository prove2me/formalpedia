-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.topologically_transitive_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:56.078982+00:00
-- url     : https://prove2.me/submissions/4ade949e-038e-43c0-bfad-c0cf086e8d93

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_iterate_eq_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_nonzero_mem_open


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    MulAction.IsTopologicallyTransitive (IterateMulAct Complex.exp) ℂ := by
  refine ⟨?_⟩
  intro U V hU hUne hV hVne
  obtain ⟨w, hwV, hw0⟩ := exists_nonzero_mem_open hV hVne
  obtain ⟨n, _, z, hzU, hzw⟩ := exists_iterate_eq_nonzero hU hUne hw0
  exact ⟨⟨n⟩, w, ⟨z, hzU, hzw⟩, hwV⟩
end ExponentialJuliaSetMisiurewicz
