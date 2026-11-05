-- Prove2me | solution 1 for GaussianSynthesis.arbitrary_fresh_columns_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/9ade7bcb-ed81-49fc-8049-deeab29f86b7

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_centerColumn_image
import Theorems.Thm_GaussianSynthesis_centerPlus_image

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (xs : List (Int × Int)) :
    InCenterImage (sumCenterColumns xs) := by
  induction xs with
  | nil => simp [InCenterImage, sumCenterColumns, mixedCenterN]
  | cons x xs ih => exact centerPlus_image _ _ (centerColumn_image x.1 x.2) ih
end GaussianSynthesis
