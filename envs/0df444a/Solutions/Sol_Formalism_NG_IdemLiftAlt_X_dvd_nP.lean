-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.X_dvd_nP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:37.729037+00:00
-- url     : https://prove2.me/submissions/b31dee2d-76b1-4427-9d39-d3e30170f1c2

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (k : ℕ) : X ∣ nP k := by
  induction k with
  | zero => exact dvd_refl _
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R * (3 * nP k - 2 * nP k ^ 2), by simp only [nP]; rw [hR]; ring⟩
end Formalism.NG.IdemLiftAlt
