-- Prove2me | solution 1 for Erdos266.not_neg_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:31.993729+00:00
-- url     : https://prove2.me/submissions/5dce032c-e897-4c8b-b3d3-315b813cf9e6

module
public import Mathlib
public import Definitions.Def_Erdos266_Glue

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution {a : ℕ → ℕ} (hpos : ∀ n, 1 ≤ a n) {t : ℚ} (ht : 0 ≤ t) :
    ¬ ∃ n : ℕ, t = -(a n) := by
  rintro ⟨n, rfl⟩
  have h1 : (1 : ℚ) ≤ (a n : ℚ) := by exact_mod_cast hpos n
  linarith
end Erdos266
