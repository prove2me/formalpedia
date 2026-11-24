-- Prove2me | solution 1 for FiniteEnergyPlane.embeddedFastPlaneSet_nonempty_of_isReebTrajectory
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:41:13.422807+00:00
-- url     : https://prove2.me/submissions/133b2cc3-c944-4f30-971e-0b6db4c12ba8

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_local_page_family
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem embeddedFastPlaneSet_nonempty_of_isReebTrajectory_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (h0 : (embeddedFastPlaneSet H J P {y 0} γ).Nonempty) (t : ℝ) (ht : 0 ≤ t) :
    (embeddedFastPlaneSet H J P {y t} γ).Nonempty := by
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
  have hS0 : ∀ x ∈ energySurface H, x ≠ 0 := by
    rintro x hx rfl
    have := hH.2.2 0 hx
    simp at this
  have hproj : ∀ x ∈ energySurface H, proj H x = x := by
    intro x hx
    have hex : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := (hH.2.1 x (hS0 x hx)).exists
    have h1 : scaleToS H x = 1 := by
      unfold scaleToS
      rw [dif_pos hex]
      refine (hH.2.1 x (hS0 x hx)).unique (Classical.choose_spec hex) ⟨one_pos, ?_⟩
      rw [one_smul]; exact hx
    unfold proj
    rw [h1, one_smul]
  have hy0 : y 0 ∉ Set.range P.x := by
    obtain ⟨v, ⟨hv, hvP, hv0, -⟩, hve⟩ := h0
    have := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz v hv hvP hve 0
    rwa [Set.mem_singleton_iff.1 hv0, hproj _ (hy.1 0)] at this
  have hmiss := IsReebTrajectory.apply_not_mem_range_of_apply_zero hH P hy hy0
  have hK := hΛ (y '' Set.Icc 0 t) (isCompact_Icc.image hyc)
    (by rintro ⟨r, -, hr⟩; exact hS0 _ (hy.1 r) hr)
    (by rintro _ ⟨r, -, rfl⟩; rw [hproj _ (hy.1 r)]; exact hmiss r)
  let G : Set ℝ := {r | (embeddedFastPlaneSet H J P {y r} γ).Nonempty}
  have hclosed : IsClosed (G ∩ Set.Icc 0 t) := by
    refine IsSeqClosed.isClosed fun r r₀ hr hlim => ?_
    have hr₀ : r₀ ∈ Set.Icc 0 t := isClosed_Icc.mem_of_tendsto hlim
      (Eventually.of_forall fun k => (hr k).2)
    choose u hu using fun k => (hr k).1
    obtain ⟨φ, hφ, v, hv, hlimv⟩ := hK u fun k =>
      ⟨⟨(hu k).1.1, (hu k).1.2.1, ⟨r k, (hr k).2, (Set.mem_singleton_iff.1 (hu k).1.2.2.1).symm⟩,
        (hu k).1.2.2.2⟩, (hu k).2⟩
    have h2 := (hlimv {0} (Set.subset_univ _) isCompact_singleton 0).tendsto_at
      (Set.mem_singleton 0)
    have h3 : Tendsto (fun k => u (φ k) 0) atTop (𝓝 (v 0)) := by
      have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℂ) (V 1) 0).continuous.tendsto
        _).comp h2
      simpa [Function.comp_def] using this
    have h4 : Tendsto (fun k => u (φ k) 0) atTop (𝓝 (y r₀)) := by
      have : (fun k => u (φ k) 0) = fun k => y (r (φ k)) :=
        funext fun k => Set.mem_singleton_iff.1 (hu (φ k)).1.2.2.1
      rw [this]
      exact (hyc.tendsto r₀).comp (hlim.comp hφ.tendsto_atTop)
    exact ⟨⟨v, ⟨hv.1.1, hv.1.2.1, tendsto_nhds_unique h3 h4, hv.1.2.2.2⟩, hv.2⟩, hr₀⟩
  have hsub : Set.Icc 0 t ⊆ G := by
    refine hclosed.Icc_subset_of_forall_mem_nhdsWithin h0 fun r hr => ?_
    obtain ⟨⟨u, hu⟩, -⟩ := hr
    obtain ⟨ε, hε, U, hU, -⟩ :=
      exists_local_page_family H hH J hJ P hcz γ y hy r u hu 1 le_rfl
    exact mem_nhdsWithin_of_mem_nhds
      (mem_of_superset (ball_mem_nhds r hε) fun x hx => ⟨_, hU.2 x hx⟩)
  exact hsub ⟨ht, le_rfl⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (h0 : (embeddedFastPlaneSet H J P {y 0} γ).Nonempty) (t : ℝ) (ht : 0 ≤ t) :
    (embeddedFastPlaneSet H J P {y t} γ).Nonempty :=
  embeddedFastPlaneSet_nonempty_of_isReebTrajectory_aux H hH J hJ P hcz γ hΛ y hy h0 t ht
