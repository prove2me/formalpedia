-- Prove2me | solution 1 for Erdos1063.W_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:53:35.353831+00:00
-- url     : https://prove2.me/submissions/31e9d4d4-3b2d-43f3-a4e8-3d6af0fffad5

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_W_dvd

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k)
    (hne : {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}.Nonempty) : W k ≤ n k := by
  unfold n
  obtain ⟨h2k, i0, hi0, -, hgood⟩ := Nat.sInf_mem hne
  have hd := W_dvd h2k hk hi0 hgood
  exact (Nat.le_of_dvd (by omega) hd).trans (Nat.sub_le _ _)
end Erdos1063
