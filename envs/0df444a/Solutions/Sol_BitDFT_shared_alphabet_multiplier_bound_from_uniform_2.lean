-- Prove2me | solution 2 for BitDFT.shared_alphabet_multiplier_bound_from_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:50:36.131989+00:00
-- url     : https://prove2.me/submissions/7a3b7396-f8cd-4f3e-bcff-facb1545c940

import Definitions.Def_BitDFT_Encoding
import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_shared_alphabet_multiplier_bound
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages
theorem solution (A M : MultitapeTM) (T : ℕ → ℝ)
    (hM : BitDFT.Multiplier M T) : BitDFT.Multiplier (right A M) T := by
  intro q hq
  exact BitDFT.shared_alphabet_multiplier_bound A M q (T q) (hM q hq)
