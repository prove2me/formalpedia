-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.iterate_T_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:43.617276+00:00
-- url     : https://prove2.me/submissions/b07cab75-fdfa-468a-94f5-22005d66575c

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Theorems.Thm_CollatzEndpointTransport_Terras_T_modEq

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution :
    ∀ (i j n n' : ℕ), n ≡ n' [MOD 2 ^ (i + j)] →
      T^[i] n ≡ T^[i] n' [MOD 2 ^ j] := by
  intro i
  induction i with
  | zero => intro j n n' h; simpa using h
  | succ i ih =>
      intro j n n' h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      apply ih
      apply T_modEq (H := i + j)
      rwa [show i + 1 + j = i + j + 1 by ring] at h
end CollatzEndpointTransport.Terras
