-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.eq_top_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.801889+00:00
-- url     : https://prove2.me/submissions/11a6dc69-063b-4a1d-9c48-703b2cc5d561

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_perp_ne_bot
import Theorems.Thm_CompanionTheory_D_gk_admitted_eq_zero_of_mem_perp
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {G : Type} (A : G → Matrix ι ι ℂ) (hadj : ∀ g, ∃ g', A g' = (A g)ᴴ)
    (N : Submodule ℂ (ι → ℂ))
    (hN : ∀ W : Submodule ℂ (ι → ℂ), W ≠ ⊥ → (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) →
      (∀ U : Submodule ℂ (ι → ℂ), U ≠ ⊥ → (∀ g, ∀ w ∈ U, A g *ᵥ w ∈ U) → U ≤ W → U = W) → W ≤ N) :
    N = ⊤ := by
  set T : Submodule ℂ (ι → ℂ) := sSup {W | (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ N} with hT
  have hTN : T ≤ N := sSup_le fun W hW => hW.2
  have hTs : ∀ g, ∀ w ∈ T, A g *ᵥ w ∈ T := by
    intro g
    have : T ≤ T.comap (Matrix.toLin' (A g)) := by
      refine sSup_le fun W hW w hw => ?_
      have hWT : W ≤ T := le_sSup hW
      simpa using hWT (hW.1 g w hw)
    intro w hw
    simpa using this hw
  have hPs : ∀ g, ∀ w ∈ perp T, A g *ᵥ w ∈ perp T := by
    intro g w hw x hx
    obtain ⟨g', hg'⟩ := hadj g
    rw [star_mulVec, ← dotProduct_mulVec, ← hg']
    exact hw _ (hTs g' x hx)
  by_contra hne
  have hTne : T ≠ ⊤ := fun e => hne (top_le_iff.1 (e ▸ hTN))
  obtain ⟨W, ⟨hW0, hWs, hWP⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ (ι → ℂ))).has_min
    {W | W ≠ ⊥ ∧ (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ perp T} ⟨perp T, perp_ne_bot T hTne, hPs, le_rfl⟩
  have hWN : W ≤ N := hN W hW0 hWs fun U hU0 hUs hUW => by
    by_contra hUne
    exact hmin U ⟨hU0, hUs, hUW.trans hWP⟩ (lt_of_le_of_ne hUW hUne)
  have hWT : W ≤ T := le_sSup ⟨hWs, hWN⟩
  apply hW0
  rw [eq_bot_iff]
  intro y hy
  exact eq_zero_of_mem_perp (hWT hy) (hWP hy)
end CompanionTheory.D.gk.admitted
