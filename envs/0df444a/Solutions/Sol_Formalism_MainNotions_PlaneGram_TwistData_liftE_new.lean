-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.liftE_new
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:41.776508+00:00
-- url     : https://prove2.me/submissions/1504726a-5569-402d-b977-52a0b1d51675

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_offE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
section Gen
variable {σ : Type} [Fintype σ]
end Gen
section Letter
variable {L : Type} [DecidableEq L] {r : ℕ}
end Letter
section Der
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
end Der
section App
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
variable {I : Type} [Fintype I]
end App
section AppL
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
end AppL
namespace TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
private theorem liftE_apply_eq_sum_elim (α : D.EA) (x : D.ML × Fin D.r) :
    D.liftE p α x = Sum.elim (fun b => α (Sum.inl b, x.2))
      (Sum.elim (fun _ => 0) (Sum.elim (fun s => α (Sum.inr s, x.2) / D.P p s) (fun _ => 0))) x.1 := by
  rfl
end TwistData
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hP : 0 < D.P p t) (α : D.EA) (ρ1 δ1 κ1 : Fin D.r →₀ ℕ) :
    D.liftE p (offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ1 + D.P p t • (δ1 + (divE (D.P p t) (letE α (Sum.inr t)) - κ1)))) =
      onLetter (D.mw t) (divE (D.P p t) ρ1 + δ1) + (D.liftE p α - onLetter (D.mw t) κ1) := by
  ext ⟨y, a⟩
  rcases y with b | t' | t' | t'
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · by_cases h : t' = t
    · subst h
      simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
      first
        | (rw [← mul_add, Nat.add_mul_div_left _ _ hP]; omega)
        | (rw [Nat.add_mul_div_left _ _ hP]; omega)
        | omega
    · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw, h]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
end Formalism.MainNotions.PlaneGram.TwistData
