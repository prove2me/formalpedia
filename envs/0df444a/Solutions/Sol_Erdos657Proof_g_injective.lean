-- Prove2me | solution 1 for Erdos657Proof.g_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:00.603802+00:00
-- url     : https://prove2.me/submissions/7e97bdfa-a6e5-40d4-8843-bd1d4d19c30b

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (k : ℕ) : Function.Injective (g (k := k)) := by
  intro U V h
  have hN : ∑ i ∈ U.map Fin.valEmbedding, 2 ^ i = ∑ i ∈ V.map Fin.valEmbedding, 2 ^ i := by
    simp only [sum_map, Fin.valEmbedding_apply]
    simp only [g] at h
    exact_mod_cast h
  exact map_injective Fin.valEmbedding (geomSum_injective le_rfl hN)
end Erdos657Proof
