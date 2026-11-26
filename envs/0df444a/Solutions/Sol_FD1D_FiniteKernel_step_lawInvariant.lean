-- Prove2me | solution 1 for FD1D.FiniteKernel.step_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:26.371066+00:00
-- url     : https://prove2.me/submissions/65b07b9d-a25a-4ded-81e0-5d9eaf7a4ee0

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
theorem _root_.solution [DecidableEq α] {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) :
    LawInvariant (K.step μ) e := by
  intro y
  rw [mass_step, mass_step,
    ← Equiv.sum_comp (e : α ≃ α) (fun x => μ.mass x * K x (e y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [hμ, hK]
end FD1D.FiniteKernel
