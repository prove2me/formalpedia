-- Prove2me | solution 1 for FD1D.FiniteKernel.tendsto_expect_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:42.236073+00:00
-- url     : https://prove2.me/submissions/cf048e63-a84d-4dd2-bc03-c5ac4900bdf9

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
import Theorems.Thm_FD1D_FiniteKernel_tendsto_iterate_mass

set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
namespace FD1D.FiniteKernel
theorem _root_.solution
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) (f : α → ℝ) :
    Tendsto (fun n => (K.iterate n μ).expect f) atTop (𝓝 (π.expect f)) := by
  have hmass := tendsto_iterate_mass K hirr hloop π hπ μ
  rw [tendsto_pi_nhds] at hmass
  unfold FiniteLaw.expect
  apply tendsto_finsetSum
  intro x _
  exact (hmass x).mul_const (f x)
end FD1D.FiniteKernel
