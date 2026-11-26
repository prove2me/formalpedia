-- Prove2me | solution 1 for Bsv.StrictSignature.strictSig_injective
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T11:40:59.7078+00:00
-- url     : https://prove2.me/submissions/c5f14315-9863-4299-8b34-58dceb4b6db4

import Definitions.Def_bsv_strict_signature
import Theorems.Thm_Bsv_StrictSignature_strictSig_eq
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

open Bsv.StrictSignature


theorem solution (b₁ b₂ r s : List Byte)
    (h₁ : strictSig b₁ = some (r, s)) (h₂ : strictSig b₂ = some (r, s)) :
    b₁ = b₂ := by
  rw [strictSig_eq _ _ _ h₁, strictSig_eq _ _ _ h₂]
