-- Prove2me | solution 1 for FirstPassageLinearTransport.card_landingBad_le_shellBad_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:15.032958+00:00
-- url     : https://prove2.me/submissions/783198bc-5fd8-4f6e-a400-53c706716d9a

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_landingBad_subset_insert_shellBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    (landingBad q t).card ≤ (shellInitialWindowBad (q - 1) t).card + 1 := by
  have hcard := Finset.card_le_card (landingBad_subset_insert_shellBad hq t)
  exact hcard.trans (Finset.card_insert_le _ _)
end FirstPassageLinearTransport
