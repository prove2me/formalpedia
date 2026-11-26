-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:38.604838+00:00
-- url     : https://prove2.me/submissions/83ec8144-f3eb-4d2a-9845-9f00a8c16b6a

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_filter_mod_mem
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_mod_pow_two
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H M K : ℕ} (hHM : H ≤ M) (hKH : K ≤ H) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by
  classical
  let S : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun x => H - K ≤ oddCount H (x : ℕ))
  have hset :
      (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => H - K ≤ oddCount H n) =
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
  exact card_residues_with_oddCount_ge_sub H K hKH
end CollatzEndpointTransport.Terras
