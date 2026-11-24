-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.chatA_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:56.751816+00:00
-- url     : https://prove2.me/submissions/fff59934-c13d-4b6b-a1f4-2b7e8da80ea3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ)
    (l : Fin m) (γ : Fin m → ℂ) (hγ : ∀ j, j ≠ l → γ j = 0) :
    chatA E u (Pi.single l 1) γ = γ l • qminor E (skip1 l) (skip1 l) u := by
  unfold chatA
  rw [Finset.sum_eq_single l (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ l) h)]
  · rw [Finset.sum_eq_single l (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ l) h)]
    · congr 1
      rw [Pi.single_eq_same, mul_one, ← two_mul, pow_mul]
      norm_num
    · simp [Pi.single_apply, hj]
  · exact Finset.sum_eq_zero fun j _ => by simp [hγ i hi]
end Formalism.FourierDecayAlt.Q.Adapted
