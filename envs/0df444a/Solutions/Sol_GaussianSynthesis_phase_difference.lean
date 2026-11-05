-- Prove2me | solution 1 for GaussianSynthesis.phase_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/6e341a63-02c8-4381-87fa-1dafb127ca9c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_mulI_difference

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (q : Nat) (u v : GInt) :
    repeatI q (gaussianDifference u v) =
      gaussianDifference (repeatI q u) (repeatI q v) := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [repeatI,ih,mulI_difference]
end GaussianSynthesis
