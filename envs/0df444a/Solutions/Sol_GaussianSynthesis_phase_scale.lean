-- Prove2me | solution 1 for GaussianSynthesis.phase_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/e6ecca6d-c245-44f6-93b5-0c0f01f3d338

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_mulI_scale


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (q : Nat) (k : Int) (z : GInt) :
    repeatI q (scale k z) = scale k (repeatI q z) := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [repeatI,ih,mulI_scale]
end GaussianSynthesis
