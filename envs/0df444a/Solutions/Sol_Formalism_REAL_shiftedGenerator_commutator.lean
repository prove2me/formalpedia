-- Prove2me | solution 1 for Formalism.REAL.shiftedGenerator_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:54.208333+00:00
-- url     : https://prove2.me/submissions/1a8bff87-2de7-4b14-9914-feca71af7e7b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (v : ℂ) (a b c d : Fin n) :
    E c d * Tm E v a b - Tm E v a b * E c d =
      (if d = a then Tm E v c b else 0) - (if b = c then Tm E v a d else 0) := by
  have hc := hE c d a b
  have hcomm : E c d * (if a = b then algebraMap ℂ A v else 0) =
      (if a = b then algebraMap ℂ A v else 0) * E c d := by
    by_cases hab : a = b
    · simp only [if_pos hab]
      exact (Algebra.commutes v (E c d)).symm
    · simp only [if_neg hab, mul_zero, zero_mul]
  have key : E c d * Tm E v a b - Tm E v a b * E c d =
      E c d * E a b - E a b * E c d := by
    unfold Tm
    rw [mul_add, add_mul, hcomm]
    abel
  rw [key, hc]
  unfold Tm
  by_cases h1 : d = a
  · by_cases h2 : b = c
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
  · by_cases h2 : b = c
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2]
end Formalism.REAL
