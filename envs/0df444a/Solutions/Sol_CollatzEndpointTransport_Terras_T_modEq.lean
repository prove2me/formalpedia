-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.T_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:08:19.29196+00:00
-- url     : https://prove2.me/submissions/a7f7105a-eddf-439f-bfed-db0db982802e

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Theorems.Thm_CollatzEndpointTransport_Terras_modEq_of_two_mul

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution {H n n' : ℕ} (h : n ≡ n' [MOD 2 ^ (H + 1)]) :
    T n ≡ T n' [MOD 2 ^ H] := by
  have hdvd : (2 : ℕ) ∣ 2 ^ (H + 1) := dvd_pow_self 2 (Nat.succ_ne_zero H)
  have h2 : n % 2 = n' % 2 := h.of_dvd hdvd
  apply modEq_of_two_mul
  rcases Nat.even_or_odd n with he | ho
  · have hn : n % 2 = 0 := Nat.even_iff.mp he
    have hn' : n' % 2 = 0 := by omega
    rw [two_mul_T_of_even hn, two_mul_T_of_even hn']
    exact h
  · have hn : n % 2 = 1 := Nat.odd_iff.mp ho
    have hn' : n' % 2 = 1 := by omega
    rw [two_mul_T_of_odd hn, two_mul_T_of_odd hn']
    exact Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 h)
end CollatzEndpointTransport.Terras
