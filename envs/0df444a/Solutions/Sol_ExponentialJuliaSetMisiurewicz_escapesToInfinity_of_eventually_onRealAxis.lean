-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_eventually_onRealAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:50.298859+00:00
-- url     : https://prove2.me/submissions/b15961fa-1d95-40e0-99ea-8d0c36b849f3

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_escapesToInfinity_of_im_eq_zero

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} {m : ℕ}
    (hm : OnRealAxis (expIterate m z)) : EscapesToInfinity z := by
  have htail := escapesToInfinity_of_im_eq_zero hm
  intro R
  obtain ⟨N, hN⟩ := htail R
  refine ⟨m + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := hN (N + k) (Nat.le_add_right N k)
  calc
    R ≤ ‖expIterate (N + k) (expIterate m z)‖ := h
    _ = ‖expIterate (N + k + m) z‖ :=
      congrArg norm (Function.iterate_add_apply exponentialMap (N + k) m z).symm
    _ = ‖expIterate (m + N + k) z‖ := by
      congr 2
      omega
end ExponentialJuliaSetMisiurewicz
