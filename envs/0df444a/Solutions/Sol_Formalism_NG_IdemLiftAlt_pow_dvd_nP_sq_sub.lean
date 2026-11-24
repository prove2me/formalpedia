-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.pow_dvd_nP_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:41.23961+00:00
-- url     : https://prove2.me/submissions/2adae3ac-9b9b-4e36-ab3e-cfda3c45a378

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
theorem _root_.solution (k : ℕ) : ∃ U : ℤ[X], nP k ^ 2 - nP k = (X ^ 2 - X) ^ (2 ^ k) * U := by
  induction k with
  | zero => exact ⟨1, by simp [nP]⟩
  | succ k ih =>
    obtain ⟨U, hU⟩ := ih
    refine ⟨U ^ 2 * (4 * (nP k ^ 2 - nP k) - 3), ?_⟩
    have h : nP (k + 1) ^ 2 - nP (k + 1) =
        (nP k ^ 2 - nP k) ^ 2 * (4 * (nP k ^ 2 - nP k) - 3) := by
      simp only [nP]; ring
    rw [h, hU, pow_succ 2 k, pow_mul]; ring
end Formalism.NG.IdemLiftAlt
