-- Prove2me | solution 1 for Erdos1063.cambie_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:12.84721+00:00
-- url     : https://prove2.me/submissions/00617819-8c35-4cfb-8a9e-2cf4681ea1f7

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_P2M_Erdos1063_exists_exception__4b25d7e991f6
public import Theorems.Thm_Erdos1063_lcm_facts
public import Theorems.Thm_Erdos1063_cambie_good

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) :
    k * (Finset.Icc 1 (k - 1)).lcm id ∈ {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k} := by
  obtain ⟨hL0, hL2⟩ := lcm_facts hk
  have h2k : 2 * k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by nlinarith
  refine ⟨h2k, 0, by omega, ?_, ?_⟩
  · intro hdiv
    apply exists_exception' (by omega) h2k
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hdiv
    · exact cambie_good hk hpos hi
  · intro i hi hne
    exact cambie_good hk (Nat.pos_of_ne_zero hne) hi
end Erdos1063
