-- Prove2me | solution 1 for BandParity.apply_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:55.622089+00:00
-- url     : https://prove2.me/submissions/5e1c3fcd-f807-473c-adb3-0525ca8f9084

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_quartic_values


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution {n : ZMod p} : χ n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ MulChar.map_zero χ⟩
  by_contra hn
  rcases quartic_values χ hχ hn with h' | h' | h' | h' <;> rw [h'] at h <;> revert h <;> decide
end BandParity
