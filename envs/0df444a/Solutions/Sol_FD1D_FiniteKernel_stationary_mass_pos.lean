-- Prove2me | solution 1 for FD1D.FiniteKernel.stationary_mass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:24.543804+00:00
-- url     : https://prove2.me/submissions/f3a4fb32-49f2-443d-8e98-4a28f2d592cb

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_pow_nonneg
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ : FiniteLaw α} (hμ : K.IsStationary μ) (y : α) :
    0 < μ.mass y := by
  have hex : ∃ x, 0 < μ.mass x := by
    by_contra h
    push_neg at h
    have hz : ∀ x, μ.mass x = 0 :=
      fun x => le_antisymm (h x) (μ.mass_nonneg x)
    have : ∑ x, μ.mass x = 0 := by simp [hz]
    linarith [μ.sum_mass]
  obtain ⟨x, hx⟩ := hex
  obtain ⟨n, hxy⟩ := hirr x y
  have hterm : 0 < μ.mass x * K.pow n x y :=
    mul_pos hx hxy
  calc
    0 < μ.mass x * K.pow n x y := hterm
    _ ≤ ∑ z, μ.mass z * K.pow n z y :=
      Finset.single_le_sum
        (fun z _ => mul_nonneg (μ.mass_nonneg z) (K.pow_nonneg n z y))
        (Finset.mem_univ x)
    _ = (K.iterate n μ).mass y := (K.mass_iterate n μ y).symm
    _ = μ.mass y := by rw [hμ.iterate n]
end FD1D.FiniteKernel
