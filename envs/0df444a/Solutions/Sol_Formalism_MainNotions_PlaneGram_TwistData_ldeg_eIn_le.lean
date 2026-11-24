-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:35.130847+00:00
-- url     : https://prove2.me/submissions/c3e35ee3-7fc4-44af-8862-b71861c29c6b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_eIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {p : ℕ} (hp : 0 < p) {ζ : D.EM} (h : D.GoodE p ζ) (i : D.ML) :
    ldeg (eIn D.outP ζ) i ≤ D.dUp i := by
  rw [ldeg_eIn]
  unfold GoodE at h
  obtain ⟨_, _, h3, h4, _⟩ := h
  split_ifs with ho
  · exact Nat.zero_le _
  · rcases i with b | t | t | t
    · exact (h3 b).le
    · exact (ho rfl).elim
    · have hP : 1 ≤ D.P p t := Nat.one_le_pow _ _ hp
      show ldeg ζ (D.mw t) ≤ D.dT t
      have h4t := h4 t
      nlinarith [Nat.zero_le (ldeg ζ (D.mw t))]
    · exact (ho rfl).elim
end Formalism.MainNotions.PlaneGram.TwistData
