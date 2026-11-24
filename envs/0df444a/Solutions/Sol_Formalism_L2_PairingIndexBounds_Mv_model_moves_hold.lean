-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.model_moves_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:11.703662+00:00
-- url     : https://prove2.me/submissions/289db42d-d407-4fc7-ac76-9fcd66006bcb

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_sum_reps_eq_zero
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_sum_reps_ind

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
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution : ModelMoves := by
  intro k _ A B _ _ c hc A₁ A₂ B₁ B₂ hB₁ h22 hA SA SB hSA hSB
  funext t
  have hL : (∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A)))) t
      = ∑ a ∈ SA, ∑ b ∈ SB, c b (t + a) * ind (A₁ : Set A) (t + a) := by
    simp only [Finset.sum_apply]; rfl
  have inner : ∀ u : A, ∑ b ∈ SB, c b u * ind (A₁ : Set A) u
      = (SB.card : k) * (ind (A₁ : Set A) u * ind (A₂ : Set A) u) := by
    intro u
    by_cases hu1 : u ∈ A₁
    · rw [ind_of_mem (show u ∈ (A₁ : Set A) from hu1)]
      by_cases hu2 : u ∈ A₂
      · rw [ind_of_mem (show u ∈ (A₂ : Set A) from hu2)]
        rw [Finset.sum_congr rfl (fun b hb => by rw [h22 b (hSB.1 b hb) u hu2])]
        simp
      · rw [ind_of_not_mem (show u ∉ (A₂ : Set A) from hu2)]
        have hex : ∃ b₀ ∈ B₂, c b₀ u ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hu2 (hA u hu1 hcon)
        obtain ⟨b₀, hb₀, hne⟩ := hex
        have := sum_reps_eq_zero B₁ B₂ SB hSB (fun b => c b u) (fun x y => hc.2.1 x y u)
          (fun x hx => (hB₁ x).mp hx u hu1) b₀ hb₀ hne
        simp only [mul_one, mul_zero]
        exact this
    · rw [ind_of_not_mem (show u ∉ (A₁ : Set A) from hu1)]
      simp
  rw [hL, Finset.sum_congr rfl (fun a _ => inner (t + a)), ← Finset.mul_sum, sum_reps_ind A₁ A₂ SA hSA t]
  rfl
end Formalism.L2.PairingIndexBounds.Mv
