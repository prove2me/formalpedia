-- Prove2me | solution 1 for Erdos266.f_cast
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:45:42.743275+00:00
-- url     : https://prove2.me/submissions/0729a0b9-cff7-4a41-9342-92e23231bc9f


import Definitions.Def_Erdos266_Defs
import Definitions.Def_Erdos266_Glue
import Definitions.Def_Erdos266_Reduction
set_option autoImplicit false


open Erdos266
open Finset
variable {a : ℕ → ℕ}
theorem _root_.solution (i n : ℕ) :
    f i ((a n : ℕ) : ℝ)
      = (((∏ k ∈ range i, ((a n : ℚ) + tSeq k))⁻¹ : ℚ) : ℝ) := by
  simp [f]

