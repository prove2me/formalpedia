-- Prove2me | solution 1 for BandParity.t_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:01.480693+00:00
-- url     : https://prove2.me/submissions/dbfdc92e-0752-414c-93b7-a13f8aaee788

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
theorem _root_.solution : t (χ ^ 3) = -t χ := by
  simp only [t, S, cosetSum_pow_three hχ]
  rw [show star gi = -gi by decide, show star (-gi) = gi by decide]; ring
end BandParity
