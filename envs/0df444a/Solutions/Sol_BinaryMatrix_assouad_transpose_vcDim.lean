-- Prove2me | solution 1 for BinaryMatrix.assouad_transpose_vcDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:28.395799+00:00
-- url     : https://prove2.me/submissions/664b0d4a-bd63-4e47-bf9c-2f7e0cb4dabd

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix
public import Theorems.Thm_BinaryMatrix_shatters_iff
public import Theorems.Thm_BinaryMatrix_transpose_shatters_imp_shatters

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix
namespace BinaryMatrix
theorem _root_.solution {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.vcDim ≤ d) :
    M.transpose.vcDim ≤ 2 ^ (d + 1) - 1 := by
  -- By contradiction: if M^T.vcDim ≥ 2^(d+1), extract a large shattered set
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ M.transpose.vcDim := by omega
  -- vcDim = shatterer.sup card. Extract a shattered set of size ≥ 2^(d+1).
  -- Use Finset.le_sup_iff with ⊥ < 2^(d+1) (since 2^(d+1) > 0)
  have hpos : (⊥ : ℕ) < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  -- Extract shattered set from vcDim bound using le_sup_iff
  obtain ⟨S, hS_mem, hS_card⟩ := (Finset.le_sup_iff hpos).mp hge
  -- S ∈ shatterer means M^T.toFinsetFamily.Shatters S
  rw [Finset.mem_shatterer] at hS_mem
  -- Convert to our shatters definition
  have hS_shat : M.transpose.shatters S := (shatters_iff M.transpose S).mpr hS_mem
  -- Apply the coding lemma
  obtain ⟨T, hT_card, hT_shat⟩ := transpose_shatters_imp_shatters M S hS_shat hS_card
  -- Convert M.shatters T to M.toFinsetFamily.Shatters T, then get vcDim ≥ d+1
  have hT_mathlib : M.toFinsetFamily.Shatters T := (shatters_iff M T).mp hT_shat
  have hvc_ge : d + 1 ≤ M.vcDim := by
    calc d + 1 = T.card := hT_card.symm
    _ ≤ M.vcDim := hT_mathlib.card_le_vcDim
  omega
end BinaryMatrix
