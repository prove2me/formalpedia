-- Prove2me | solution 1 for Erdos1219.erdosRado_unbalanced_wo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:47:04.494656+00:00
-- url     : https://prove2.me/submissions/249ca2ba-83e3-4ffd-9964-ead7fcfcaa92

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_good_case
import Theorems.Thm_Erdos1219_no_good_case

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {f : W → W → Bool} (hf : ∀ x y, f x y = f y x)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (c : Bool) :
    (∃ H : Set W, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H) := by
  by_cases hg : ∃ α, IsGood f c μ α
  · obtain ⟨α, hα⟩ := hg
    exact Or.inr (good_case hf hα)
  · push Not at hg
    obtain ⟨H, hH, hHc⟩ := no_good_case hf hμ hW hord hg
    exact Or.inl ⟨H, hH.trans hW, hHc⟩
end Erdos1219
