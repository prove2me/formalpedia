-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_mod_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:55.330236+00:00
-- url     : https://prove2.me/submissions/1e949177-d66e-45d4-bd12-30f25f5affcd

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_parityVec_congr


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H n : ℕ) :
    oddCount H (n % (2 ^ H)) = oddCount H n := by
  unfold oddCount
  rw [parityVec_congr]
  show n % 2 ^ H % 2 ^ H = n % 2 ^ H
  exact Nat.mod_mod _ _
end CollatzEndpointTransport.Terras
