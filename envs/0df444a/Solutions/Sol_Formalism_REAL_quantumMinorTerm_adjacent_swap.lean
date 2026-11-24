-- Prove2me | solution 1 for Formalism.REAL.quantumMinorTerm_adjacent_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:38.094672+00:00
-- url     : https://prove2.me/submissions/f7425c32-7445-4600-a9a6-fac0ceb6ca5f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Theorems.Thm_Formalism_REAL_shiftedGenerator_quadratic
import Theorems.Thm_Formalism_REAL_prod_ofFn_alternating_sum

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) = 0 := by
  unfold exchangeTwo_self_eq_one
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k hk₁ hk₂
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hk₁ (by rw [h, Fin.val_castSucc]))
      (fun h => hk₂ (by rw [h, Fin.val_succ]))
  refine prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) hi ?_ ?_ ?_ ?_
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Function.comp_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, Function.comp_apply, hfix k hk₁ hk₂]
  · have key := shiftedGenerator_quadratic E hE (u - ((i : ℕ) : ℂ)) (u - (((i : ℕ) + 1 : ℕ) : ℂ))
      (by push_cast; ring) (a (σ i.castSucc)) (a (σ i.succ)) (b i.castSucc) (b i.succ)
    have e0 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e1 : (⟨(i : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact key
end Formalism.REAL
