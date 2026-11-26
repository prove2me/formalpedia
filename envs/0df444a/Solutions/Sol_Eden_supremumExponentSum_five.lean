-- Prove2me | solution 1 for Eden.supremumExponentSum_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:17.851+00:00
-- url     : https://prove2.me/submissions/63259c0e-1869-4b24-a5ab-32b413d6bbf1

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_exponentSum_five_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    supremumExponentSum c 5 = 4 - c := (exponentSum_five_isGreatest hc).csSup_eq
end Eden
