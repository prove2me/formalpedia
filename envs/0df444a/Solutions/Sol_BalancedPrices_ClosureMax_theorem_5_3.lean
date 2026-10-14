-- Prove2me | solution 1 for BalancedPrices.ClosureMax.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:58:09.670289+00:00
-- url     : https://prove2.me/submissions/e240e70c-8285-4bcb-a55d-643b2f12196d

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition
import Theorems.Thm_BalancedPrices_ClosureMax_closure_max_a
import Theorems.Thm_BalancedPrices_ClosureMax_closure_max_b
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
    (hsup : IsSupporting Vsp vt (ALG vf) vf) :
    BalancedPrices.Extension.IsPricingRule F (pr vt) ∧
      BalancedPrices.Extension.Balanced nul α β F Fam vf (ALG vf) (pr vt) := by
  refine ⟨hprice vt (fun i => (hsup i).1), ?_⟩
  intro x hx
  exact ⟨closure_max_a nul F hdown Fam Vsp hV α β hα hβ hFam ALG hALG hcons
      pr hprice hbal vf vt hvf hsup x hx,
    fun x' hx' => closure_max_b nul F hdown Fam Vsp hV α β hα hβ hFam ALG hALG
      hcons pr hprice hbal vf vt hvf hsup x x' hx hx'⟩


