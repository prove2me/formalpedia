-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rho_side_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:11.669532+00:00
-- url     : https://prove2.me/submissions/7030d50f-b6f0-4f36-80c1-96b68d228ee2

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_rho_antitone_of_interlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.RhoSide := by
  unfold C7.RhoSide C7.Between
  intro k u u' ρ l Y hl hlk hI hB i hi
  have hi' : 1 ≤ i ∧ i ≤ k - 1 := by simpa using hi
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro hli
    have h1 := hI l (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI l i hl hli hi'.2
    have h3 : ρ l + 1 / 2 ≤ min (u l) (u' l) := le_min h1.1 h1.2.1
    linarith
  · intro hil
    have h1 := hI (l - 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI i (l - 1) hi'.1 (by omega) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    have h3 : max (u l) (u' l) + 1 / 2 ≤ ρ (l - 1) := by
      rcases le_total (u l) (u' l) with h | h
      · rw [max_eq_right h]; exact h1.2.2.2
      · rw [max_eq_left h]; exact h1.2.2.1
    linarith
end Formalism.FourierDecayAlt.P
