-- Prove2me | solution 1 for CostSharingPNE.Char.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:33:27.172309+00:00
-- url     : https://prove2.me/submissions/4fb43026-8685-4362-a44c-ef2be18868e9

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Theorems.Thm_CostSharingPNE_Char_gwsv_guarantees_pne
import Theorems.Thm_CostSharingPNE_Char_theorem_1_only_if

open CostSharingPNE.Char

/-- Utilities only read shares `f (W r) i S` with `W r ∈ 𝕎` and `i ∈ S`, so two rule families
agreeing there have the same equilibria. -/
lemma CSPThm1Aux_transfer {n : ℕ} (𝕎 : Set (Welfare n)) (f g : Welfare n → Rule n)
    (hfg : ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S, f W i S = g W i S)
    (hg : GuaranteesPNE 𝕎 g) : GuaranteesPNE 𝕎 f := by
  intro m hm W hW A hA
  obtain ⟨a, ha, hN⟩ := hg m hm W hW A hA
  have hU : ∀ (b : Fin n → Finset (Fin m)) (i : Fin n), utility W f b i = utility W g b i := by
    intro b i
    unfold utility
    apply Finset.sum_congr rfl
    intro r hr
    apply hfg _ (hW r)
    simp [players, hr]
  refine ⟨a, ha, fun i b hb => ?_⟩
  rw [hU, hU]
  exact hN i b hb

theorem solution (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (h𝕎 : 𝕎.Nonempty)
    (f : Welfare n → Rule n) :
    GuaranteesPNE 𝕎 f ↔
      ∃ ω : WeightSystem n, ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
        f W i S = gwsv ω (distributed (f W)) i S := by
  constructor
  · exact theorem_1_only_if n hn 𝕎 h𝕎 f
  · rintro ⟨ω, hω⟩
    exact CSPThm1Aux_transfer 𝕎 f (fun W => gwsv ω (distributed (f W))) hω
      (gwsv_guarantees_pne n hn 𝕎 ω (fun W => distributed (f W)))
