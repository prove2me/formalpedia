-- Prove2me | solution 1 for BandParity.cosetSum_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:53.72312+00:00
-- url     : https://prove2.me/submissions/296e0479-e937-41d0-b794-200219f74a8f

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) :
    cosetSum χ z = ∑ n : ZMod p, if χ n = z then (n.val : ℤ) else 0 := by
  rw [cosetSum, Finset.sum_filter]
end BandParity
