-- Prove2me | solution 1 for BandParity.cosetSum_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:41.802255+00:00
-- url     : https://prove2.me/submissions/316e9c26-bbf0-49a3-8535-b9338dac6802

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_pow_three_apply
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (z : GaussianInt) : cosetSum (χ ^ 3) z = cosetSum χ (star z) := by
  unfold cosetSum
  congr 1; ext n
  simp only [mem_filter, mem_univ, true_and, pow_three_apply hχ]
  exact ⟨fun h => h ▸ (star_star _).symm, fun h => by rw [h, star_star]⟩
end BandParity
