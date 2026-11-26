-- Prove2me | solution 1 for Erdos266.sample_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:48:28.050112+00:00
-- url     : https://prove2.me/submissions/5faadbee-bb37-4fc7-9309-46942fd566cd

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {j l : ℕ} : (bigN l : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := by
  have h : bigN l ≤ (j + 1) * bigN l := Nat.le_mul_of_pos_left _ (by omega)
  exact_mod_cast h
end Erdos266
