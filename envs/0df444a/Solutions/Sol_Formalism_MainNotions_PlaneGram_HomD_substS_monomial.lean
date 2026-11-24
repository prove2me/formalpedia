-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_substS_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:08.980808+00:00
-- url     : https://prove2.me/submissions/b61aa022-2b01-4aaf-abc7-d26bbe052345

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_X
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_congr
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_subX

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
variable {L : Type} {r : ℕ}
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α : L × Fin r →₀ ℕ) :
    HomD (ldeg α) (substS ι sg S A B (monomial α 1)) := by
  induction α using Finsupp.induction_linear with
  | zero =>
    have : (monomial (0 : L × Fin r →₀ ℕ) (1 : K)) = 1 := rfl
    rw [this, map_one]
    exact HomD_congr (fun i => (ldeg_zero i).symm) HomD_one
  | add α β hα hβ =>
    have : (monomial (α + β) (1 : K)) = monomial α 1 * monomial β 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul]
    exact HomD_congr (fun i => (ldeg_add α β i).symm) (HomD_mul hα hβ)
  | single x k =>
    rw [← X_pow_eq_monomial, map_pow, substS_X]
    induction k with
    | zero =>
      rw [pow_zero, Finsupp.single_zero]
      exact HomD_congr (fun i => (ldeg_zero i).symm) HomD_one
    | succ k ih =>
      rw [pow_succ, Finsupp.single_add]
      exact HomD_congr (fun i => (ldeg_add _ _ i).symm) (HomD_mul ih (HomD_subX sg S A B x))
end Formalism.MainNotions.PlaneGram
