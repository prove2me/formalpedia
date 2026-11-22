-- Prove2me | solution 1 for CircuitComplexity.shannon_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:21.437807+00:00
-- url     : https://prove2.me/submissions/23008d62-bd74-49b4-817f-4eae61bf0f7f

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Theorems.Thm_CircuitComplexity_card_circDesc
public import Theorems.Thm_CircuitComplexity_card_bool_fun
public import Theorems.Thm_CircuitComplexity_arith_bound

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ (d : CircDesc N (2 ^ N / (5 * N))),
        evalD (s_pos N hN) d ≠ f := by
  let s := 2 ^ N / (5 * N)
  let hs := s_pos N hN
  -- The image of evalD has strictly fewer elements than the function space
  have h_lt : ((Finset.univ : Finset (CircDesc N s)).image (evalD (N := N) (s := s) hs)).card
      < (Finset.univ : Finset (BitString N → Bool)).card := by
    calc ((Finset.univ : Finset (CircDesc N s)).image (evalD hs)).card
        ≤ (Finset.univ : Finset (CircDesc N s)).card := Finset.card_image_le
      _ = Fintype.card (CircDesc N s) := Finset.card_univ
      _ = (8 * (N + s) ^ 2) ^ s := card_circDesc N s
      _ < 2 ^ 2 ^ N := arith_bound N hN
      _ = Fintype.card (BitString N → Bool) := (card_bool_fun N).symm
      _ = (Finset.univ : Finset (BitString N → Bool)).card := (Finset.card_univ).symm
  -- By pigeonhole, some function is not in the image of evalD
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt
  exact ⟨f, fun d hd => hf (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩)⟩
end CircuitComplexity
