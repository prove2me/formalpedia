-- Prove2me | solution 1 for Cage87.vertices_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:25:33.342468+00:00
-- url     : https://prove2.me/submissions/002f2c5a-2567-4882-b648-e647d910f0dd

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Theorems.Thm_Cage87_chunk_0
public import Theorems.Thm_Cage87_chunk_1
public import Theorems.Thm_Cage87_chunk_2
public import Theorems.Thm_Cage87_chunk_3
public import Theorems.Thm_Cage87_chunk_4
public import Theorems.Thm_Cage87_chunk_5
public import Theorems.Thm_Cage87_chunk_6
public import Theorems.Thm_Cage87_chunk_7
public import Theorems.Thm_Cage87_verticesOk_mem


set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution (v : Nat) (hv : v < 768) : vertexOk adj v = true := by
  have : (0 ≤ v ∧ v < 96) ∨ (96 ≤ v ∧ v < 192) ∨ (192 ≤ v ∧ v < 288) ∨ (288 ≤ v ∧ v < 384) ∨ (384 ≤ v ∧ v < 480) ∨ (480 ≤ v ∧ v < 576) ∨ (576 ≤ v ∧ v < 672) ∨ (672 ≤ v ∧ v < 768) := by omega
  rcases this with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact verticesOk_mem adj 0 96 chunk_0 v h0.1 (by omega)
  · exact verticesOk_mem adj 96 96 chunk_1 v h1.1 (by omega)
  · exact verticesOk_mem adj 192 96 chunk_2 v h2.1 (by omega)
  · exact verticesOk_mem adj 288 96 chunk_3 v h3.1 (by omega)
  · exact verticesOk_mem adj 384 96 chunk_4 v h4.1 (by omega)
  · exact verticesOk_mem adj 480 96 chunk_5 v h5.1 (by omega)
  · exact verticesOk_mem adj 576 96 chunk_6 v h6.1 (by omega)
  · exact verticesOk_mem adj 672 96 chunk_7 v h7.1 (by omega)
end Cage87
