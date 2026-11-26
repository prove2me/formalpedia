-- Prove2me | solution 1 for FirstPassageLinearTransport.generatedFirstBadSources_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:59.802361+00:00
-- url     : https://prove2.me/submissions/c1282eef-cd29-4f75-8b5f-3ed37009b582

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_firstBadLandingEnvelope_card_le
import Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_subset_envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((generatedFirstBadSources M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
  have hcard := Finset.card_le_card
    (generatedFirstBadSources_subset_envelope
      (M := M) (L := L) (U := U) (H := H) (r := r) (t := t) hr)
  have hcardQ :
      ((generatedFirstBadSources M L U H r t).card : ℚ) ≤
        ((firstBadLandingEnvelope M L U H r t).card : ℚ) := by
    exact_mod_cast hcard
  exact hcardQ.trans (firstBadLandingEnvelope_card_le t hr hUM hsmall)
end FirstPassageLinearTransport
