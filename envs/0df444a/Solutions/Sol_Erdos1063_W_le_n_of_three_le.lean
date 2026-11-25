-- Prove2me | solution 1 for Erdos1063.W_le_n_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:08.634801+00:00
-- url     : https://prove2.me/submissions/06f2d4a9-fb12-4919-b610-0f967789de0b

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_W_le_n
public import Theorems.Thm_Erdos1063_cambie_mem

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) : W k ≤ n k :=
  W_le_n (by omega) ⟨_, cambie_mem hk⟩
end Erdos1063
