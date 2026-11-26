-- Prove2me | solution 1 for Eden.supremumExponentSum_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:13.299957+00:00
-- url     : https://prove2.me/submissions/85c18427-5e15-4279-bdcb-53f117e9de5c

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_exponentSum_four_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    supremumExponentSum c 4 = 4 := (exponentSum_four_isGreatest hc).csSup_eq
end Eden
