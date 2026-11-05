-- Prove2me | solution 1 for GaussianSynthesis.gaussian_update_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/d9a4ea59-87e5-42a9-9297-da8917c7808e

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (old fresh : GInt) :
    gaussianDifference (add old fresh) old = fresh := by
  apply GInt.ext <;> simp only [gaussianDifference,add,neg] <;> omega
end GaussianSynthesis
