-- Prove2me | solution 1 for BandParity.quartic_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:19.659161+00:00
-- url     : https://prove2.me/submissions/1cd7683d-4933-49c4-ad29-85d0b14ff764

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution {χ ψ : MulChar (ZMod p) GaussianInt} {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) (h : χ g = ψ g) : χ = ψ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨k, rfl⟩ := hg u
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]
end BandParity
