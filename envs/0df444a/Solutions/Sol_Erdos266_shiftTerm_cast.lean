-- Prove2me | solution 1 for Erdos266.shiftTerm_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:25.389482+00:00
-- url     : https://prove2.me/submissions/a812ebc5-71ac-4490-a4e3-37c0793926b6

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}
namespace Erdos266
theorem _root_.solution (n k : ℕ) :
    ((a n : ℝ) + (tSeq k : ℝ))⁻¹ = ((((a n : ℚ) + tSeq k)⁻¹ : ℚ) : ℝ) := by
  push_cast
  rfl
end Erdos266
