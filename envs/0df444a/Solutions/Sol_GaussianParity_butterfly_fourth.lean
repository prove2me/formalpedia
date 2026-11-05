-- Prove2me | solution 1 for GaussianParity.butterfly_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/ff472b3b-09a6-45de-814a-5abb372fc721

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_butterfly_square
import Theorems.Thm_GaussianParity_SameValue_symm

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    butterflyPair (butterflyPair (butterflyPair (butterflyPair (u, v)))) = (u, v) := by
  have hs := butterfly_square u v h
  have hvu : SameResidue v u := Eq.symm h
  change butterflyPair (butterflyPair (butterfly (butterfly u v).1 (butterfly u v).2)) = _
  rw [hs]
  exact butterfly_square v u hvu
end GaussianParity
