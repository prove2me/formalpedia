-- Prove2me | solution 1 for Eden.commonIndex_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:39.723841+00:00
-- url     : https://prove2.me/submissions/d8881130-5a99-465e-885c-6d4c3899d826

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
import Theorems.Thm_Eden_commonIndexCandidates_isLeast

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) : commonIndex c = 4 :=
  (commonIndexCandidates_isLeast hc).csInf_eq
end Eden
