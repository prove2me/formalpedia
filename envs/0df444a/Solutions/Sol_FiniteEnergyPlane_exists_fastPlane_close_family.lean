-- Prove2me | solution 1 for FiniteEnergyPlane.exists_fastPlane_close_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T15:17:22.571194+00:00
-- url     : https://prove2.me/submissions/3216ef57-3f51-42a2-a057-7f450cba672a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_CylClose
import Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_fastPlane
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_of_infDist_le
import Theorems.Thm_FiniteEnergyPlane_isEmbeddedPlane_of_isCylCloseTo
import Theorems.Thm_FiniteEnergyPlane_range_shiftA_eq_imp_of_family
import Theorems.Thm_FiniteEnergyPlane_fderiv_family_add_smul_eq_zero
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Glue: `exists_fastPlane_close_family` from the five children. -/
theorem exists_fastPlane_close_family_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        IsEmbeddedPlane (fun z => g (z, t)) ∧ IsCylCloseTo H ε (fun z => g (z, t)) u) ∧
      (∀ c ∈ Set.Ioo (-r) r, ∀ t ∈ Set.Ioo (-r) r, ∀ c' ∈ Set.Ioo (-r) r, ∀ t' ∈ Set.Ioo (-r) r,
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t') ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  obtain ⟨δ, hδ, hwin, r₀, hr₀, g, hg, hg0, hmem, hclose⟩ :=
    exists_jHolomorphic_family_of_fastPlane H hH J hJ P hcz u hu huP hue (max l 2)
      (le_trans hl (le_max_left _ _))
  have hg1 : ∀ m : ℕ, m ≤ max l 2 → ContDiffOn ℝ m g (Set.univ ×ˢ Set.Ioo (-r₀) r₀) :=
    fun m hm => hg.of_le (by exact_mod_cast hm)
  have htr0 : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0 :=
    (hmem 0 ⟨by linarith, hr₀⟩).2.2.2.2.2.2.2
  obtain ⟨ε₀, hε₀, hemb⟩ := isEmbeddedPlane_of_isCylCloseTo H hH J hJ P u hu huP hue
  obtain ⟨r₁, ⟨hr₁, hr₁r⟩, hc₁⟩ := hclose (min ε ε₀) (lt_min hε hε₀)
  obtain ⟨r₂, ⟨hr₂, hr₂r⟩, hsep⟩ := range_shiftA_eq_imp_of_family H hH P u
    (fun z => hu.1.2.1 z (Set.mem_univ z)) huP hue r₀ hr₀ g
    ((hg1 1 (le_trans hl (le_max_left _ _))).of_le (by norm_num)) hg0
    (fun t ht z => (hmem t ht).2.1 z) hclose htr0
  set r := min r₁ r₂ with hr_def
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsub₁ : Set.Ioo (-r) r ⊆ Set.Ioo (-r₁) r₁ := fun x hx =>
    ⟨by linarith [hx.1, min_le_left r₁ r₂], by linarith [hx.2, min_le_left r₁ r₂]⟩
  have hsub₂ : Set.Ioo (-r) r ⊆ Set.Ioo (-r₂) r₂ := fun x hx =>
    ⟨by linarith [hx.1, min_le_right r₁ r₂], by linarith [hx.2, min_le_right r₁ r₂]⟩
  have hsub₀ : Set.Ioo (-r) r ⊆ Set.Ioo (-r₀) r₀ := fun x hx =>
    ⟨by linarith [(hsub₁ hx).1], by linarith [(hsub₁ hx).2]⟩
  have hfast : ∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) := by
    intro t ht
    obtain ⟨hs, hne, hJh, -, hend, ⟨C, hC⟩, -, -⟩ := hmem t (hsub₀ ht)
    exact isFastPlane_of_infDist_le H hH J hJ P u hu huP δ hδ hwin (min ε ε₀) _ hs hne hJh hend
      (hc₁ t (hsub₁ ht)) C hC
  have hgr : ContDiffOn ℝ (max l 2 : ℕ) g (Set.univ ×ˢ Set.Ioo (-r) r) :=
    hg.mono (Set.prod_mono subset_rfl hsub₀)
  refine ⟨r, hr, g, hgr.of_le (by exact_mod_cast le_max_left _ _), hg0, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hs, hne, -, -, hend, -, -, -⟩ := hmem t (hsub₀ ht)
    have hcl := hc₁ t (hsub₁ ht)
    refine ⟨hfast t ht, hend, ?_, ?_⟩
    · refine hemb _ (hs.of_le (by exact_mod_cast le_top)) hne ?_
      intro z
      obtain ⟨h1, h2, h3⟩ := hcl z
      exact ⟨h1.trans (min_le_right _ _), h2.trans (min_le_right _ _), h3.trans (min_le_right _ _)⟩
    · intro z
      obtain ⟨h1, h2, h3⟩ := hcl z
      exact ⟨h1.trans (min_le_left _ _), h2.trans (min_le_left _ _), h3.trans (min_le_left _ _)⟩
  · intro c hc t ht c' hc' t' ht' h
    exact hsep c (hsub₂ hc) t (hsub₂ ht) c' (hsub₂ hc') t' (hsub₂ ht') h
  · intro z t ht Δ δt lam h0
    obtain ⟨-, -, -, hX, hend, -, ⟨C, hC⟩, htr⟩ := hmem t (hsub₀ ht)
    exact fderiv_family_add_smul_eq_zero H hH J hJ P δ hδ hwin r g
      (hgr.of_le (by exact_mod_cast le_max_right _ _))
      (fun t' ht' => (hmem t' (hsub₀ ht')).2.2.1) t ht (hfast t ht) hend hX C hC htr z Δ δt lam h0

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        IsEmbeddedPlane (fun z => g (z, t)) ∧ IsCylCloseTo H ε (fun z => g (z, t)) u) ∧
      (∀ c ∈ Set.Ioo (-r) r, ∀ t ∈ Set.Ioo (-r) r, ∀ c' ∈ Set.Ioo (-r) r, ∀ t' ∈ Set.Ioo (-r) r,
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t') ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 :=
  exists_fastPlane_close_family_aux H hH J hJ P hcz u hu huP hue l hl ε hε
