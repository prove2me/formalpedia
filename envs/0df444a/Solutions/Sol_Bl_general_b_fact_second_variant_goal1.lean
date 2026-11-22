-- Prove2me | solution 1 for Bl.general_b_fact_second_variant.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:17.159682+00:00
-- url     : https://prove2.me/submissions/1b68b825-a047-49f8-bfb8-c3c50bd50a60

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_second_variant
namespace Bl.general_b_fact_second_variant
theorem _root_.solution :
  ∀ {k : Type u_1} [inst : Field.{u_1} k] (τ : RingHom.{u_1, u_1} k k),
  (∀ (x : k),
      Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ x)) x) →
    ∀ (θ : k),
      Ne.{u_1 + 1} (HSub.hSub.{u_1, u_1, u_1} θ (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ θ)) 0 →
        Eq.{1} (Nat.card.{u_1} k)
          (HPow.hPow.{0, 0, 0}
            (Nat.card.{u_1}
              (Subtype.{u_1 + 1} fun (x : k) ↦ Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} τ x) x))
            2)  := by
  intro k _ τ hτ θ hθ
  have hb : ∀ x : k, τ ((x - τ x) / (θ - τ θ)) = (x - τ x) / (θ - τ θ) := by
    intro x
    rw [map_div₀, map_sub, map_sub, hτ, hτ, ← neg_sub x (τ x), ← neg_sub θ (τ θ), neg_div_neg_eq]
  have ha : ∀ x : k, τ (x - (x - τ x) / (θ - τ θ) * θ) = x - (x - τ x) / (θ - τ θ) * θ := by
    intro x
    have e : (x - τ x) / (θ - τ θ) * (θ - τ θ) = x - τ x := div_mul_cancel₀ _ hθ
    rw [map_sub, map_mul, hb x]
    linear_combination e
  let e : k ≃ {x : k // τ x = x} × {x : k // τ x = x} :=
    { toFun := fun x => (⟨x - (x - τ x) / (θ - τ θ) * θ, ha x⟩, ⟨(x - τ x) / (θ - τ θ), hb x⟩)
      invFun := fun p => p.1.1 + p.2.1 * θ
      left_inv := fun x => by
        show x - (x - τ x) / (θ - τ θ) * θ + (x - τ x) / (θ - τ θ) * θ = x
        ring
      right_inv := by
        rintro ⟨⟨a, ha'⟩, ⟨b, hb'⟩⟩
        have h1 : (a + b * θ - τ (a + b * θ)) / (θ - τ θ) = b := by
          rw [map_add, map_mul, ha', hb', div_eq_iff hθ]; ring
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show a + b * θ - (a + b * θ - τ (a + b * θ)) / (θ - τ θ) * θ = a
          rw [h1]; ring
        · show (a + b * θ - τ (a + b * θ)) / (θ - τ θ) = b
          exact h1 }
  rw [Nat.card_congr e, Nat.card_prod, sq]
end Bl.general_b_fact_second_variant
