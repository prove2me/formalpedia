-- Prove2me | solution 1 for GaussianSynthesis.arbitrary_fresh_columns_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/f470368b-7dd3-4b1a-8408-6f08355767cf

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_arbitrary_fresh_columns_image

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (xs : List (Int × Int)) :
    mixedCenterN (sumCenterColumns xs).sumB (sumCenterColumns xs).sumD / (-32)
      = (sumCenterColumns xs).total := by
  have h := arbitrary_fresh_columns_image xs
  simp only [InCenterImage] at h
  rw [h]
  omega
end GaussianSynthesis
