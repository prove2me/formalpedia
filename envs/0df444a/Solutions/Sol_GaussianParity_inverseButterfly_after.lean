-- Prove2me | solution 1 for GaussianParity.inverseButterfly_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/9aa5520d-c7c6-4117-bb19-3aaa7e35d85b

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext
import Theorems.Thm_GaussianParity_butterfly_sameResidue
import Theorems.Thm_GaussianParity_butterfly_square
import Theorems.Thm_GaussianParity_inverseButterfly_eq_swap

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    inverseButterfly (butterfly u v).1 (butterfly u v).2 = (u, v) := by
  rw [inverseButterfly_eq_swap _ _ (butterfly_sameResidue u v h)]
  have hs := butterfly_square u v h
  have hl := congrArg (fun p : GInt × GInt => p.1) hs
  have hr := congrArg (fun p : GInt × GInt => p.2) hs
  exact Prod.ext hr hl
end GaussianParity
