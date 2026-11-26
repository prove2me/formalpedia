-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_dyadic_shell_filter_mod_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:27:16.50151+00:00
-- url     : https://prove2.me/submissions/029a73b8-ebf7-4c0e-800c-764d666fe744

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_Ico_filter_mod_mem_of_dvd

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H M : ℕ} (hHM : H ≤ M) (S : Finset (Fin (2 ^ H))) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n =>
        (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ H)) ∈ S)).card =
      2 ^ (M - H) * S.card := by
  have hq : 0 < 2 ^ H := pow_pos (by omega) _
  have hbase : 2 ^ H ∣ 2 ^ M := pow_dvd_pow 2 hHM
  have hlength : 2 ^ (M - H) * 2 ^ H = 2 ^ M :=
    pow_sub_mul_pow 2 hHM
  have hupper : 2 ^ M + 2 ^ (M - H) * 2 ^ H = 2 ^ (M + 1) := by
    rw [hlength, pow_succ]
    omega
  have h := card_Ico_filter_mod_mem_of_dvd
    (base := 2 ^ M) (blocks := 2 ^ (M - H)) (q := 2 ^ H)
    hq hbase S
  simpa only [hupper] using h
end CollatzEndpointTransport.Terras
