-- Prove2me | solution 1 for BSLambda.adj_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:57.007823+00:00
-- url     : https://prove2.me/submissions/08dcbf47-e240-4617-aa80-9804bafffc99

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_exists_eq_flipSet_singleton_of_hammingDist_eq_one
public import Theorems.Thm_BSLambda_flipSet_singleton_injective


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (ν : Input V → ℝ) (x : Input V) :
    (adj f *ᵥ ν) x = ∑ i : V, adj f x (flipSet x {i}) * ν (flipSet x {i}) := by
  classical
  have himg : ∑ y ∈ Finset.univ.image fun i : V ↦ flipSet x {i}, adj f x y * ν y
      = ∑ i : V, adj f x (flipSet x {i}) * ν (flipSet x {i}) :=
    Finset.sum_image fun a _ b _ hab ↦ flipSet_singleton_injective x hab
  rw [← himg]
  change ∑ y : Input V, adj f x y * ν y = _
  refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy ↦ ?_).symm
  suffices h0 : adj f x y = 0 by rw [h0, zero_mul]
  rw [adj_apply]
  refine if_neg fun h ↦ hy ?_
  obtain ⟨w, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one h.1
  exact Finset.mem_image.2 ⟨w, Finset.mem_univ w, rfl⟩
end BSLambda
