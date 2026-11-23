-- Prove2me | solution 1 for FasterWCTFPTAS.Main.observation_4_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:29:46.79475+00:00
-- url     : https://prove2.me/submissions/2752831b-584c-47f7-9076-8bbccf97c6b3

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

open FasterWCTFPTAS.Main

theorem solution {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : ℕ) (hi : i ≤ n) (δ δ' : ℝ) (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (A B C : Set (Pt m)) (hA : A ⊆ DP m p w i) (hB : B ⊆ DP m p w i) (hC : C ⊆ DP m p w i)
    (hAB : IsRepSet m p w i δ A B) (hBC : IsRepSet m p w i δ' B C) :
    IsRepSet m p w i (δ + δ') A C := by
  refine ⟨Set.Subset.trans hAB.1 hBC.1, fun σ' σ hσC => ?_⟩
  obtain ⟨σB, hσBB, hcostB⟩ := hBC.2 σ' σ hσC
  obtain ⟨σA, hσAA, hcostA⟩ := hAB.2 σ' σB hσBB
  exact ⟨σA, hσAA, by linarith⟩
