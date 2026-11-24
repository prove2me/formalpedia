-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lambda_side_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:36.586775+00:00
-- url     : https://prove2.me/submissions/bf832ad1-3bee-4e41-9470-f15fb3f76012

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing

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
theorem _root_.solution : C7.LamSide := by
  unfold C7.LamSide C7.LamInterlaces
  rintro k r u u' lam l Y hl hlk ⟨hA, hL⟩ ⟨-, hL'⟩ - i
  constructor
  · intro hli
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 1 := ⟨⟨l - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam i ≤ lam j := hA.antitone hji
    have h1 := (hL j).1 (by omega)
    have h2 := (hL' j).1 (by omega)
    rw [show (j : ℕ) + 1 = l by omega] at h1 h2
    exact lt_min (lt_of_le_of_lt hi1 h1) (lt_of_le_of_lt hi1 h2)
  · intro hil
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 2 := ⟨⟨l - 2, by omega⟩, rfl⟩
    have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam j ≤ lam i := hA.antitone hij
    have h1 := (hL j).2 (by omega)
    have h2 := (hL' j).2 (by omega)
    rw [show (j : ℕ) + 2 = l by omega] at h1 h2
    exact max_lt (lt_of_lt_of_le h1 hi1) (lt_of_lt_of_le h2 hi1)
end Formalism.FourierDecayAlt.P
