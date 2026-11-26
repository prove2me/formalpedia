-- Prove2me | solution 1 for FD1D.FiniteKernel.orbit_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:53.460272+00:00
-- url     : https://prove2.me/submissions/f538663b-678a-47e6-96de-bc043bea4806

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    K.orbit μ n x ≤ 1 := by
  rw [orbit_eq_iterate, ← (K.iterate n μ).sum_mass]
  exact Finset.single_le_sum
    (fun y _ => (K.iterate n μ).mass_nonneg y) (Finset.mem_univ x)
end FD1D.FiniteKernel
