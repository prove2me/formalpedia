-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:11.979594+00:00
-- url     : https://prove2.me/submissions/f5e807f4-f7dc-48f1-938c-3056eec3f140

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_real_orbit


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (hz : z.im = 0) :
    EscapesToInfinity z := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (R - z.re)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hre := (expIterate_real_orbit hz n).2
  have hR : R ≤ (expIterate n z).re := by
    linarith
  exact hR.trans <| (le_abs_self _).trans (Complex.abs_re_le_norm _)
end ExponentialJuliaSetMisiurewicz
