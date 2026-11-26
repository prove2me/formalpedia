-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.modEq_of_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:54.738804+00:00
-- url     : https://prove2.me/submissions/d2e9c8eb-2e1c-4262-9cdf-eeb109a44c9f

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution {H a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ (H + 1)]) : a ≡ b [MOD 2 ^ H] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  push_cast at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hp : ((2 : ℤ)) ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [hp] at hk
  linarith
end CollatzEndpointTransport.Terras
