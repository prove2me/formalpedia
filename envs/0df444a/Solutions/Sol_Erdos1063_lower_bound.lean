-- Prove2me | solution 1 for Erdos1063.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:05.922071+00:00
-- url     : https://prove2.me/submissions/15cd69f3-f1ca-4379-895f-bfea314a1fce

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_W_le_n
public import Theorems.Thm_Erdos1063_W_le_n_of_three_le

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k := by
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    exact W_le_n le_rfl ⟨4, by decide⟩
  · exact W_le_n_of_three_le h3
end Erdos1063
