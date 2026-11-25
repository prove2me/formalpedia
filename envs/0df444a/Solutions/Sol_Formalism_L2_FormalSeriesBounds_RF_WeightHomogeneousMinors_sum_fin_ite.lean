-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.sum_fin_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:30.726001+00:00
-- url     : https://prove2.me/submissions/a43cc1e7-85c7-459e-8e5b-ae86cb6d71fb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {R : Type} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution (k c0 : ℕ) : (∑ c : Fin k, if (c : ℕ) = c0 then 1 else 0) = if c0 < k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c0, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro hc; exact hb (Fin.ext hc)
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hc
    exact h (by rw [← hc]; exact c.2)
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
