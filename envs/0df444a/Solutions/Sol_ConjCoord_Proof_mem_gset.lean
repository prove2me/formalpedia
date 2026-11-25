-- Prove2me | solution 1 for ConjCoord.Proof.mem_gset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:22.05663+00:00
-- url     : https://prove2.me/submissions/65e17f7d-43a4-48d3-9c23-db83deec2cc5

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
public import Theorems.Thm_ConjCoord_Proof_mem_Icc_of_sq_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ gset m ↔ v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
      (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10) := by
  unfold gset box3
  rw [mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have e1 := sq_nonneg v.1
  have e2 := sq_nonneg v.2.1
  have e3 := sq_nonneg v.2.2
  exact mem_product.mpr ⟨mem_Icc_of_sq_le (by linarith), mem_product.mpr
    ⟨mem_Icc_of_sq_le (by linarith), mem_Icc_of_sq_le (by linarith)⟩⟩
end ConjCoord.Proof
