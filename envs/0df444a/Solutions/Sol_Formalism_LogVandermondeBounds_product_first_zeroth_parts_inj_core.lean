-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.inj_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:50.525102+00:00
-- url     : https://prove2.me/submissions/9375b7ca-128b-4371-8aed-06e5733f54b0

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_ne
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (ψ : (ι → H) → K)
    (hψ : ∀ (v : ι) (h : ι → H), ∑ c : H, ψ ((Pi.mulSingle v c : ι → H) * h) = 0)
    (h0 : ∀ a : ι → {c : H // c ≠ 1}, ψ (fun w => (a w : H)) = 0) :
    ∀ h, ψ h = 0 := by
  classical
  suffices key : ∀ n, ∀ h : ι → H, (univ.filter (fun w => h w = 1)).card = n → ψ h = 0 from
    fun h => key _ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn
    by_cases hall : ∀ w, h w ≠ 1
    · exact h0 (fun w => ⟨h w, hall w⟩)
    · simp only [not_forall, not_not] at hall
      obtain ⟨v, hv⟩ := hall
      have hsum := hψ v h
      rw [Finset.sum_eq_single (1 : H)] at hsum
      · simpa using hsum
      · intro c _ hc
        apply ih _ _ _ rfl
        rw [← hn]
        have hset : univ.filter (fun w => ((Pi.mulSingle v c : ι → H) * h) w = 1)
            = (univ.filter (fun w => h w = 1)).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hwv : w = v
          · subst hwv
            rw [mulSingle_mul_apply_self, hv, mul_one]
            simp [hc]
          · rw [mulSingle_mul_apply_ne v w c h hwv]
            simp [hwv]
        rw [hset]
        exact Finset.card_erase_lt_of_mem (by simp [hv])
      · intro h1
        exact absurd (Finset.mem_univ _) h1
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
