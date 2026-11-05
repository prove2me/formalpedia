-- Prove2me | solution 1 for GaussianParity.raiseTo_sameValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/88454412-8b56-4700-8bc1-a6b163668969

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_piIter_add

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (x : Fraction) (e : Nat) (h : x.exponent ≤ e) :
    SameValue (raiseTo x e) x := by
  unfold SameValue raiseTo
  simp only
  rw [← piIter_add]
  have he : x.exponent + (e - x.exponent) = e := by omega
  rw [he]
end GaussianParity
