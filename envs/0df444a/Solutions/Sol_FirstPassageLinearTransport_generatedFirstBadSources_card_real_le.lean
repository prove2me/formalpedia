-- Prove2me | solution 1 for FirstPassageLinearTransport.generatedFirstBadSources_card_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:06.636875+00:00
-- url     : https://prove2.me/submissions/7c039005-90f1-4544-a5a8-f294c812406f

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Theorems.Thm_FirstPassageLinearTransport_generatedFirstBadSources_card_le


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
    ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q * ((landingBad q t).card : ℝ) := by
  have h := generatedFirstBadSources_card_le (H := H) t hr hUM hsmall
  exact_mod_cast h
end FirstPassageLinearTransport
