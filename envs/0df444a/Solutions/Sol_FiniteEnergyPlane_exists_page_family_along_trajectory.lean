-- Prove2me | solution 1 for FiniteEnergyPlane.exists_page_family_along_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:43:43.601867+00:00
-- url     : https://prove2.me/submissions/d6f4a562-5904-4fcd-ad14-8dbd9e8d6f51

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_local_page_family
import Theorems.Thm_FiniteEnergyPlane_exists_isPageFamilyOn_Ioo_glue
import Theorems.Thm_FiniteEnergyPlane_embeddedFastPlaneSet_nonempty_of_isReebTrajectory



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_page_family_along_trajectory_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (l : ℕ) (hl : 1 ≤ l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo (-δ) τ) U ∧
      ∀ z, U (0, z) = v z := by
  obtain ⟨δ, hδ, U₀, hU₀, hU₀0, -⟩ :=
    exists_local_page_family H hH J hJ P hcz γ y hy 0 v hv l hl
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hU₀
  let S : Set ℝ := {s | ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo (-δ) s) U ∧
    ∀ z, U (0, z) = v z}
  have hmono : ∀ s ∈ S, ∀ r ≤ s, r ∈ S := by
    rintro s ⟨U, hU, h0⟩ r hr
    exact ⟨U, ⟨hU.1.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hr) subset_rfl),
      fun t ht => hU.2 t (Set.Ioo_subset_Ioo_right hr ht)⟩, h0⟩
  have hδS : δ ∈ S := ⟨U₀, hU₀, hU₀0⟩
  suffices h : τ ∈ S from ⟨δ, hδ, h⟩
  by_contra hτS
  have hub : ∀ s ∈ S, s ≤ τ := fun s hs => le_of_not_gt fun h => hτS (hmono s hs τ h.le)
  have hbdd : BddAbove S := ⟨τ, hub⟩
  have hs0 : 0 < sSup S := hδ.trans_le (le_csSup hbdd hδS)
  obtain ⟨u, hu⟩ := embeddedFastPlaneSet_nonempty_of_isReebTrajectory H hH J hJ P hcz γ hΛ y hy
    ⟨v, hv⟩ (sSup S) hs0.le
  obtain ⟨ε, hε, W, hW, -⟩ :=
    exists_local_page_family H hH J hJ P hcz γ y hy (sSup S) u hu l hl
  rw [Real.ball_eq_Ioo] at hW
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨δ, hδS⟩
    (max_lt hs0 (show sSup S - ε < sSup S by linarith))
  obtain ⟨m, hm1, hm2⟩ := exists_between hs
  have hm0 : 0 < m := (le_max_left _ _).trans_lt hm1
  have hmε : sSup S - ε < m := (le_max_right _ _).trans_lt hm1
  have hsS' := le_csSup hbdd hsS
  obtain ⟨U, hU, hU0⟩ := hsS
  obtain ⟨U', hU', hU'U⟩ := exists_isPageFamilyOn_Ioo_glue H hH J hJ P hcz γ y hy l hl (-δ) s
    (sSup S - ε) (sSup S + ε) m U W hU hW ⟨by linarith, hm2⟩ ⟨hmε, by linarith⟩
  have : sSup S + ε ∈ S :=
    ⟨U', hU', fun z => by rw [hU'U 0 ⟨by linarith, hm0.le⟩ z, hU0]⟩
  linarith [le_csSup hbdd this]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (l : ℕ) (hl : 1 ≤ l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo (-δ) τ) U ∧
      ∀ z, U (0, z) = v z :=
  exists_page_family_along_trajectory_aux H hH J hJ P hcz γ hΛ y hy v hv l hl τ hτ
