-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexBlockMove_potential_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:43.200804+00:00
-- url     : https://prove2.me/submissions/8d62e246-15df-442a-bcc7-3a9d4c07e58f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_simplicialLt_colex
public import Theorems.Thm_BooleanIsoperimetry_familyUp_potential_lt_of_blockLt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : compressionPotential A' < compressionPotential A := by
  have heq := h.1
  have hne := h.2.1
  have hlt := h.2.2
  subst heq
  refine familyUp_potential_lt_of_blockLt hne ?_
  intro S hsub hdisj
  have hcard : ({i} : Finset (Fin N)).card = ({j} : Finset (Fin N)).card := by
    rw [Finset.card_singleton, Finset.card_singleton]
  have hlt_simp : simplicialLt {j} {i} := by
    have h_nat : cubeToNat {i} < cubeToNat {j} := by
      unfold cubeToNat
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact Nat.pow_lt_pow_right (by norm_num) hlt
    refine ⟨Or.inr ⟨hcard, by omega⟩, ?_⟩
    rintro (H | ⟨_, H⟩) <;> omega
  exact blockReplace_simplicialLt_colex hsub hdisj hcard hlt_simp
end BooleanIsoperimetry
