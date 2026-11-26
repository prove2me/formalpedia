-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:59.039185+00:00
-- url     : https://prove2.me/submissions/e0775f50-c7d3-4f74-b86b-a603a7cf1213

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_filter_mod_mem
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_mod_pow_two
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H M K : ℕ} (hHM : H ≤ M) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by
  classical
  let S : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun x => oddCount H (x : ℕ) ≤ K)
  have hset :
      (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => oddCount H n ≤ K) =
        (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n =>
            (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ H)) ∈ S) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_univ,
      true_and]
    rw [oddCount_mod_pow_two]
  rw [hset, card_dyadic_shell_filter_mod_mem hHM S]
  congr 1
  exact card_residues_with_oddCount_le H K
end CollatzEndpointTransport.Terras
