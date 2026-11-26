-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellBad_pullback_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:24.605151+00:00
-- url     : https://prove2.me/submissions/ab216bc3-4846-4b53-9c40-5d1b25a86d8f

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_shellBad_pullback_subset

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    (shellBad (firstPassagePullback p S) M).card ≤
      (shellBad (extendedWindow p) M).card +
        (transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M))).card := by
  calc
    _ ≤ ((shellBad (extendedWindow p) M) ∪
        transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M))).card :=
      Finset.card_le_card (shellBad_pullback_subset p S hM)
    _ ≤ _ := Finset.card_union_le _ _
end FirstPassageLinearTransport
