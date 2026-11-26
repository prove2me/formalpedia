-- Prove2me | solution 1 for Erdos266.f_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:45:41.946013+00:00
-- url     : https://prove2.me/submissions/627ec674-3b40-424a-af12-699b1f2939af


import Definitions.Def_Erdos266_Enumeration
import Definitions.Def_Erdos266_Defs
set_option autoImplicit false


open Erdos266
open Finset
theorem _root_.solution (i : ℕ) (q : ℚ) :
    f i (q : ℝ) = ((∏ j ∈ range i, (q + tSeq j))⁻¹ : ℚ) := by
  simp [f]

