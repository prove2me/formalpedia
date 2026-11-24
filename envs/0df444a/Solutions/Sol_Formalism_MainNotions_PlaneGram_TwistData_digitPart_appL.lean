-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_appL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:23.851751+00:00
-- url     : https://prove2.me/submissions/3d19fa57-6396-494c-a6a5-4cd47204ae4d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bin_onLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_inClass_new
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_inClass_update
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_new
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_letE_liftE_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_opS_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
private theorem digitPart_approx_term_lemma_4 (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cl : Fin D.r → ℕ) (e : K) (ρ0 δ0 κ0 : Fin D.r →₀ ℕ) (α : D.EA) (c : K) :
    c • D.digitPart p ρ'' (if cl = (fun a => α (Sum.inr t, a) % D.P p t) then
      monomial (Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ0 + D.P p t • (δ0 + (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)) - κ0))))
        (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)))) else 0) =
      if (fun a => ρ0 a % D.P p t) = ρ'' t then
        D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (D.digitPart p (Function.update ρ'' t cl) (monomial α c))
      else 0 := by
  have hsh : ∀ L : D.EM, D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (monomial L c) =
      monomial (onLetter (D.mw t) (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) + (L - onLetter (D.mw t) κ0))
        (c * (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.letE L (D.mw t)))) := by
    intro L
    rw [opS_apply, Formalism.MainNotions.PlaneGram.ddiv_monomial', Formalism.MainNotions.PlaneGram.bin_onLetter, monomial_mul, smul_monomial, smul_eq_mul,
      one_mul, mul_left_comm]
  by_cases h2 : (fun a => ρ0 a % D.P p t) = ρ'' t
  · rw [if_pos h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial, digitPart_monomial]
      by_cases hQ : ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a
      · rw [if_pos ((D.inClass_new p t ρ'' α ρ0 _).2 ⟨fun a => congrFun h2 a, hQ⟩),
          if_pos ((D.inClass_update p t ρ'' α cl).2 ⟨h1, hQ⟩), smul_monomial, smul_eq_mul, hsh,
          D.liftE_new p t hP, letE_liftE_mw]
      · rw [if_neg (fun h => hQ ((D.inClass_new p t ρ'' α ρ0 _).1 h).2),
          if_neg (fun h => hQ ((D.inClass_update p t ρ'' α cl).1 h).2), smul_zero, map_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero, digitPart_monomial,
        if_neg (fun h => h1 ((D.inClass_update p t ρ'' α cl).1 h).1), map_zero]
  · rw [if_neg h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial,
        if_neg (fun h => h2 (funext ((D.inClass_new p t ρ'' α ρ0 _).1 h).1)), smul_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero]
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
theorem _root_.solution {I : Type} [Fintype I] (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cls : I → Fin D.r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin D.r →₀ ℕ))
    (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ'' (appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G) =
      ∑ s, if (fun a => ρ' s a % D.P p t) = ρ'' t then
        D.opS t (divE (D.P p t) (ρ' s) + δ s) (κ s) (cf s)
          (D.digitPart p (Function.update ρ'' t (cls s)) G) else 0 := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.appL, Formalism.MainNotions.PlaneGram.lsup_monomial, digitPart_smul, Formalism.MainNotions.PlaneGram.appMon, digitPart_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact digitPart_approx_term_lemma_4 D p t hP ρ'' (cls s) (cf s) (ρ' s) (δ s) (κ s) α c
  · rw [map_add, digitPart_add, h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos h, if_pos h, if_pos h, digitPart_add, map_add]
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
end Formalism.MainNotions.PlaneGram.TwistData
