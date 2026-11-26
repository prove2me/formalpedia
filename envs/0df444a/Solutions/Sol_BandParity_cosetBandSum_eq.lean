-- Prove2me | solution 1 for BandParity.cosetBandSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:19.432036+00:00
-- url     : https://prove2.me/submissions/f3c1aaba-6825-4bd4-bc73-3dd0d56504c9

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_cosetBandSum_eq__5f1f29a5d302


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH
namespace BandParity
theorem _root_.solution (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) :=
  cosetBandSum_eq' hN hN3 hH x he he0
end BandParity
