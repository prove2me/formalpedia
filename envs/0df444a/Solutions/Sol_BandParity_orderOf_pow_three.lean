-- Prove2me | solution 1 for BandParity.orderOf_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:18.621988+00:00
-- url     : https://prove2.me/submissions/6cade1f8-4103-4d68-a08b-49decc54992e

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) :
    orderOf (χ ^ 3) = 4 := by
  rw [orderOf_pow' χ (by norm_num), hχ]; rfl
end BandParity
