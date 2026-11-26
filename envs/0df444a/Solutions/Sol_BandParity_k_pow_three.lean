-- Prove2me | solution 1 for BandParity.k_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:49.070858+00:00
-- url     : https://prove2.me/submissions/7412ced5-b4fb-4d58-a38d-ddea47004437

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_cosetSum_pow_three
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
theorem _root_.solution : k (χ ^ 3) = k χ := by
  simp only [k, S, cosetSum_pow_three hχ]; rw [show star (1 : GaussianInt) = 1 by decide,
    show star (-1 : GaussianInt) = -1 by decide]
end BandParity
