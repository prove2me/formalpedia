-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T10:23:31.184981+00:00
-- url     : https://prove2.me/submissions/97ff9b4a-24ca-4650-bd07-2e2d45bcab86

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_succ_le_of_halfPlane



namespace FiniteEnergyPlane

open scoped ContDiff

theorem tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (h0 : TendstoZeroUnif f)
    (hB : ∀ m : ℕ, ∃ B s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ B) :
    TendstoZeroCInfty f := by
  refine ⟨⟨s₀, hf⟩, ?_⟩
  intro m
  induction m with
  | zero =>
    intro ε hε
    obtain ⟨s₁, h⟩ := h0 ε hε
    exact ⟨s₁, fun s hs t => by simpa [norm_iteratedFDeriv_zero] using h s hs t⟩
  | succ j ih =>
    intro ε hε
    obtain ⟨B, sB, hBj⟩ := hB (j + 2)
    set B' := max B 1 with hB'
    have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set h := ε / (8 * B') with hh
    have hhpos : 0 < h := div_pos hε (by positivity)
    obtain ⟨sA, hA⟩ := ih (ε * h / 8) (by positivity)
    refine ⟨max (max sA sB) (s₀ + 1), fun s hs t => ?_⟩
    have hsA : sA ≤ s := le_trans (le_max_left _ _) (le_of_max_le_left hs)
    have hsB : sB ≤ s := le_trans (le_max_right _ _) (le_of_max_le_left hs)
    have hs0 : s₀ < s := by linarith [le_of_max_le_right hs]
    have key := norm_iteratedFDeriv_succ_le_of_halfPlane f s₀ hf j (s, t) hs0
      (ε * h / 8) B' h hhpos
      (by rintro ⟨q1, q2⟩ hq; exact hA q1 (hsA.trans hq) q2)
      (by
        rintro ⟨q1, q2⟩ hq
        exact (hBj q1 (hsB.trans hq) q2).trans (le_max_left _ _))
    refine key.trans ?_
    · have e1 : 2 * (ε * h / 8) / h = ε / 4 := by field_simp; ring
      have e2 : B' * h = ε / 8 := by rw [hh]; field_simp
      rw [e1, e2]; linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (h0 : TendstoZeroUnif f)
    (hB : ∀ m : ℕ, ∃ B s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ B) :
    TendstoZeroCInfty f :=
  tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd_aux f s₀ hf h0 hB
