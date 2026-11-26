-- Prove2me | solution 1 for FD1D.FiniteKernel.reaches_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:54.814693+00:00
-- url     : https://prove2.me/submissions/d3626d92-5697-4dec-98ab-0d24df320e79

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_pow_nonneg

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α)
    {x y z : α} (hxy : K.Reaches x y) (hyz : K.Reaches y z) :
    K.Reaches x z := by
  obtain ⟨m, hm⟩ := hxy
  obtain ⟨n, hn⟩ := hyz
  refine ⟨m + n, lt_of_lt_of_le (mul_pos hm hn) ?_⟩
  rw [pow_add]
  exact Finset.single_le_sum
    (fun w _ => mul_nonneg (K.pow_nonneg m x w) (K.pow_nonneg n w z))
    (Finset.mem_univ y)
end FD1D.FiniteKernel
