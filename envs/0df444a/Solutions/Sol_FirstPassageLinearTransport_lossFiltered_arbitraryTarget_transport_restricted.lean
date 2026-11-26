-- Prove2me | solution 1 for FirstPassageLinearTransport.lossFiltered_arbitraryTarget_transport_restricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:40.968624+00:00
-- url     : https://prove2.me/submissions/f1e37b30-d605-4344-8603-3eb0c062ace7

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_uniform

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y H : ℕ} (B A : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    (((lossFilteredTransportedSources M Y H B D) ∩ A).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by
  have hcard :
      (((lossFilteredTransportedSources M Y H B D) ∩ A).card : ℚ) ≤
        ((lossFilteredTransportedSources M Y H B D).card : ℚ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  exact hcard.trans
    (lossFiltered_arbitraryTarget_transport_uniform B hY hD hsmall hYM)
end FirstPassageLinearTransport
