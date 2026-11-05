-- Prove2me | solution 1 for GaussianSynthesis.dirty_update_difference_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/93c01926-3a6c-4bfe-b94f-a0d7fa73c173

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_arbitrary_fresh_columns_image

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (oldD oldB : Int) (xs : List (Int × Int)) :
    mixedCenterN
      ((oldB+(sumCenterColumns xs).sumB)-oldB)
      ((oldD+(sumCenterColumns xs).sumD)-oldD)
      = -32*(sumCenterColumns xs).total := by
  have h := arbitrary_fresh_columns_image xs
  simp only [InCenterImage, mixedCenterN] at *
  omega
end GaussianSynthesis
