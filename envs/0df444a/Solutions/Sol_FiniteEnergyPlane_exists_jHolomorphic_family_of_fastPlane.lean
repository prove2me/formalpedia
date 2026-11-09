-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jHolomorphic_family_of_fastPlane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-08T22:47:52.597484+00:00
-- url     : https://prove2.me/submissions/eb424675-dd81-489d-b5a2-900c99a190d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_CylClose
import Theorems.Thm_FiniteEnergyPlane_exists_hasEigenWind_window
import Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_window
import Theorems.Thm_FiniteEnergyPlane_contDiff_fderiv_family_of_isJHolomorphicOn
import Theorems.Thm_FiniteEnergyPlane_exists_forall_injective_fderiv_add_smul
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Glue: `exists_jHolomorphic_family_of_fastPlane` from the window, the family for a given rate,
openness of the transversality at `z = 0`, and smoothness of `∂ₜg`. -/
theorem exists_jHolomorphic_family_of_fastPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ δ < 0, (∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) ∧
      ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
        (∀ z, g (z, 0) = u z) ∧
        (∀ t ∈ Set.Ioo (-r) r,
          ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
          JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
          ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) ∧
          IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
          (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
          (∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
          ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, t) (Δ, δt) + lam • g (0, t) = 0 →
            Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
        ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
          IsCylCloseTo H ε (fun z => g (z, t)) u := by
  obtain ⟨δ, hδ, hδe, hwin⟩ := exists_hasEigenWind_window H hH J hJ P hcz
  obtain ⟨r₀, hr₀, g, hg, hg0, hmem, htr0, hclose⟩ :=
    exists_jHolomorphic_family_of_window H hH J hJ P hcz u hu huP hue δ hδ hδe hwin (max l 2)
      (le_trans hl (le_max_left _ _))
  have hg1 : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r₀) r₀) :=
    hg.of_le (by exact_mod_cast le_trans hl (le_max_left l 2))
  obtain ⟨r, ⟨hr, hrr₀⟩, htr⟩ := exists_forall_injective_fderiv_add_smul r₀ hr₀ g hg1 0 htr0
  have hsub : Set.Ioo (-r) r ⊆ Set.Ioo (-r₀) r₀ := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgr : ContDiffOn ℝ (max l 2 : ℕ) g (Set.univ ×ˢ Set.Ioo (-r) r) :=
    hg.mono (Set.prod_mono subset_rfl hsub)
  have hdt : ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) :=
    contDiff_fderiv_family_of_isJHolomorphicOn H hH J hJ (max l 2) (le_max_right _ _) r g hgr
      (fun t ht => ⟨(hmem t (hsub ht)).1, (hmem t (hsub ht)).2.1, (hmem t (hsub ht)).2.2.1⟩)
  refine ⟨δ, hδ, hwin, r, hr, g, hgr.of_le (by exact_mod_cast le_max_left _ _), hg0, ?_, ?_⟩
  · intro t ht
    obtain ⟨hs, hne, hJh, hend, hdist, hder⟩ := hmem t (hsub ht)
    exact ⟨hs, hne, hJh, hdt t ht, hend, hdist, hder, htr t ht⟩
  · intro ε hε
    obtain ⟨r', ⟨hr', hr'r₀⟩, hc⟩ := hclose ε hε
    refine ⟨min r' r, ⟨lt_min hr' hr, min_le_right _ _⟩, fun t ht => hc t ?_⟩
    exact ⟨by linarith [ht.1, min_le_left r' r], by linarith [ht.2, min_le_left r' r]⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ δ < 0, (∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) ∧
      ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
        (∀ z, g (z, 0) = u z) ∧
        (∀ t ∈ Set.Ioo (-r) r,
          ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
          JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
          ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) ∧
          IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
          (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
          (∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
          ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, t) (Δ, δt) + lam • g (0, t) = 0 →
            Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
        ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
          IsCylCloseTo H ε (fun z => g (z, t)) u :=
  exists_jHolomorphic_family_of_fastPlane_aux H hH J hJ P hcz u hu huP hue l hl
