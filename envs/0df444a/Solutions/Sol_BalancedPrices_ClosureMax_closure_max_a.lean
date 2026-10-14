-- Prove2me | solution 1 for BalancedPrices.ClosureMax.closure_max_a
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:49:43.067498+00:00
-- url     : https://prove2.me/submissions/c8c2bcfe-7787-484d-b2d5-1159ac29b6d2

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
    (x : BalancedPrices.Extension.Outcome X) (hx : x ∈ F) :
    ENNReal.ofReal ((1 / α) * (BalancedPrices.Extension.welfare vf (ALG vf) - BalancedPrices.Extension.optVal vf (Fam x))) ≤
      ∑ i, pr vt i (x i) (BalancedPrices.Extension.pre nul x i) := by
  have hvt : ∀ i, vt i ∈ Vsp i := fun i => (hsup i).1
  have hm := optVal_mono Vsp hV vt vf hvt hvf (fun i => (hsup i).2.1) (Fam x)
  have hc := hcons vf hvf vt hsup
  have heq : BalancedPrices.Extension.welfare vt (ALG vf) =
      BalancedPrices.Extension.welfare vf (ALG vf) := by
    exact Finset.sum_congr rfl (fun i _ => (hsup i).2.2)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hbal vt hvt x hx).1
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [heq] at hc
  linarith


