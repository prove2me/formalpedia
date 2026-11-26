-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.parityVec_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:03.462807+00:00
-- url     : https://prove2.me/submissions/40e08e75-3eef-4a9f-84f7-485488f456e6

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Theorems.Thm_CollatzEndpointTransport_Terras_iterate_T_modEq

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution {H n n' : ℕ} (h : n ≡ n' [MOD 2 ^ H]) :
    parityVec H n = parityVec H n' := by
  funext i
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt i.isLt
  have hstep : T^[(i : ℕ)] n ≡ T^[(i : ℕ)] n' [MOD 2 ^ (j + 1)] := by
    apply iterate_T_modEq
    rwa [show (i : ℕ) + (j + 1) = H by omega]
  have hdvd : (2 : ℕ) ∣ 2 ^ (j + 1) := dvd_pow_self 2 (Nat.succ_ne_zero j)
  have h2 : T^[(i : ℕ)] n % 2 = T^[(i : ℕ)] n' % 2 := hstep.of_dvd hdvd
  simp only [parityVec, parityBit, h2]
end CollatzEndpointTransport.Terras
