-- Prove2me | solution 1 for Eden.commonIndexDimension_eq_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:50.512804+00:00
-- url     : https://prove2.me/submissions/e6e82c47-68d2-441b-9439-70e7be683633

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
import Theorems.Thm_Eden_commonIndex_eq_four
import Theorems.Thm_Eden_commonIndexRatio_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    commonIndexDimension c = 4 + 4 / c := by
  rw [commonIndexDimension, commonIndex_eq_four hc, (commonIndexRatio_isGreatest hc).csSup_eq]
  norm_num
end Eden
