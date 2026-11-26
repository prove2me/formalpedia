-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:04.748216+00:00
-- url     : https://prove2.me/submissions/46c8c0f0-6488-448e-b9f4-de0a4c1e2813

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  rw [card_residues_with_oddCount_le]
  exact lowerBinomialSum_le_hoeffding ht hcut
end CollatzEndpointTransport.Terras
