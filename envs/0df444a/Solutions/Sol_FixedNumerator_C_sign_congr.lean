-- Prove2me | solution 1 for FixedNumerator.C_sign_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:14.844132+00:00
-- url     : https://prove2.me/submissions/330e79e0-2f55-445c-a339-fbb50dda6dee

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_quarter_parity
public import Theorems.Thm_FixedNumerator_neg_one_zpow_congr

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {a b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c := by
  apply neg_one_zpow_congr
  unfold C
  rw [Int.mul_emod, quarter_parity hb h, ← Int.mul_emod]
end FixedNumerator
