-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:10.535775+00:00
-- url     : https://prove2.me/submissions/b87b3148-d92b-4f03-ba90-816af2297638

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le_hoeffding

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
        (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) /
        (2 : ℝ) ^ H ≤
      Real.exp (-2 * t ^ 2 * H) := by
  apply (div_le_iff₀ (pow_pos (by norm_num) H)).2
  simpa [mul_comm] using card_residues_with_oddCount_le_hoeffding ht hcut
end CollatzEndpointTransport.Terras
