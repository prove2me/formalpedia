-- Prove2me | solution 1 for Erdos1063.cambie_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:09.769019+00:00
-- url     : https://prove2.me/submissions/9e750896-ddf8-47ee-9afc-4ae862f6fb53

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_cambie_mem

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) : n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id :=
  Nat.sInf_le (cambie_mem hk)
end Erdos1063
