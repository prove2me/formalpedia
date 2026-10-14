-- Prove2me | solution 1 for BalancedPrices.ClosureMax.closure_max_b
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:51:26.605596+00:00
-- url     : https://prove2.me/submissions/6de8528b-74a9-40cd-9e3c-59f34d4b5a0a

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition
import Theorems.Thm_BalancedPrices_ClosureMax_optVal_mono
open BalancedPrices.ClosureMax



theorem solution {n : ℕ} {X : Fin n → Type*}
    (nul : BalancedPrices.Extension.Outcome X) (F : Set (BalancedPrices.Extension.Outcome X))
    (hdown : BalancedPrices.Extension.DownClosed nul F)
    (Fam : BalancedPrices.Extension.Outcome X → Set (BalancedPrices.Extension.Outcome X))
    (Vsp : ∀ i, Set (X i → ℝ))
    (hV : ∀ i (f : X i → ℝ), f ∈ Vsp i → ∀ xi, 0 ≤ f xi ∧ f xi ≤ 1)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hFam : BalancedPrices.Extension.ExchFamily F Fam)
    (ALG : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.Outcome X)
    (hALG : ∀ w, (∀ i, w i ∈ VmaxSet Vsp i) → ALG w ∈ F)
    (hcons : Consistent Vsp ALG)
    (pr : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.PriceRule X)
    (hprice : ∀ w, (∀ i, w i ∈ Vsp i) → BalancedPrices.Extension.IsPricingRule F (pr w))
    (hbal : ∀ w : BalancedPrices.Extension.Valuation X, (∀ i, w i ∈ Vsp i) →
      BalancedPrices.Extension.Balanced nul α β F Fam w (ALG w) (pr w))
    (vf vt : BalancedPrices.Extension.Valuation X) (hvf : ∀ i, vf i ∈ VmaxSet Vsp i)
    (hsup : IsSupporting Vsp vt (ALG vf) vf)
    (x x' : BalancedPrices.Extension.Outcome X) (hx : x ∈ F) (hx' : x' ∈ Fam x) :
    (∑ i, pr vt i (x' i) (BalancedPrices.Extension.pre nul x i)) ≤
      ENNReal.ofReal (β * BalancedPrices.Extension.optVal vf (Fam x)) := by
  have hvt : ∀ i, vt i ∈ Vsp i := fun i => (hsup i).1
  have hm := optVal_mono Vsp hV vt vf hvt hvf (fun i => (hsup i).2.1) (Fam x)
  exact (hbal vt hvt x hx).2 x' hx' |>.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm hβ))


