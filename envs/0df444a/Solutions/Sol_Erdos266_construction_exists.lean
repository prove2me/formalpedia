-- Prove2me | solution 1 for Erdos266.construction_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:23:36.808348+00:00
-- url     : https://prove2.me/submissions/29990cd0-1511-4d0d-a680-5d7ae6e14e9c

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_one_le_aSeq
public import Theorems.Thm_Erdos266_aSeq_strictMono
public import Theorems.Thm_Erdos266_hasSum_aSeq

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ) := by
  refine ⟨aSeq, aSeq_strictMono, one_le_aSeq 0, fun i hi => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact ⟨xinf i', hasSum_aSeq i'⟩
end Erdos266
