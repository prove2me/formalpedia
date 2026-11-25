-- Prove2me | solution 1 for FiniteEnergyPlane.energySurface_diff_range_subset_image_pageMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:33:03.042372+00:00
-- url     : https://prove2.me/submissions/d34d69f0-2871-43ad-8cc5-52ee0a26ab15

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_contDiff
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_eventually_exists_eq_of_fderiv_eq_reeb
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_of_pageMap_mem
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_isPathConnected_energySurface_diff_range
import Theorems.Thm_FiniteEnergyPlane_isReebPositiveAt_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_nhdsWithin_energySurface_le_map
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pfo_ne_zero {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma pfo_proj_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := proj_mem_energySurface H hH y hy

lemma pfo_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) {r : ℝ} (hr : 0 < r) : proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface H hH x hx r hr

lemma pfo_proj_self {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : proj H x = x := by
  simpa using pfo_proj_smul hH hx one_pos

lemma pfo_eq_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ∃ r : ℝ, y = Real.exp r • proj H y := by
  obtain ⟨s, hs, hsy⟩ := (hH.2.1 _ hy).exists
  refine ⟨-Real.log s, ?_⟩
  have h := pfo_proj_smul hH hsy (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h
  rw [h, Real.exp_neg, Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma pfo_smul_eq {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x q : V n} {r : ℝ}
    (hx : H x = 1) (hq : H q = 1) (h : Real.exp r • x = q) : x = q := by
  rw [← pfo_proj_smul hH hx (Real.exp_pos r), h, pfo_proj_self hH hq]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem energySurface_diff_range_subset_image_pageMap_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (L : ℝ) (hL : 0 < L) (hLI : Set.Icc 0 L ⊆ I)
    (hyL : y L ∈ Set.range (fun z => pageMap H U (0, z))) :
    energySurface H \ Set.range P.x ⊆ pageMap H U '' (Set.Icc 0 L ×ˢ Set.univ) := by
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hU1 : ContDiffOn ℝ 1 U (I ×ˢ Set.univ) := hU.1.of_le (by exact_mod_cast hl)
  have hO : IsOpen (I ×ˢ (Set.univ : Set ℂ)) := hI.prod isOpen_univ
  have hF := contDiffOn_pageMap H hH U I hI hU1 hne
  have hFS : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), pageMap H U p ∈ energySurface H := fun p hp =>
    (pfo_proj_mem hH (hne p hp))
  have hU0 : ∀ t ∈ I, pageMap H U (t, 0) = y t := fun t ht => by
    show proj H (U (t, 0)) = _
    rw [show U (t, 0) = y t from (hU.2 t ht).1.2.2.1, pfo_proj_self hH (hy.1 t)]
  have hleaf : ∀ s ∈ I, ∀ t ∈ I, ∀ z z', pageMap H U (s, z) = pageMap H U (t, z') →
      Set.range (fun z => pageMap H U (s, z)) = Set.range (fun z => pageMap H U (t, z)) :=
    fun s hs t ht z z' h => range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ γ _ _ _ _
      (hU.2 s hs) (hU.2 t ht) z z' h
  have h0I : (0 : ℝ) ∈ I := hLI ⟨le_rfl, hL.le⟩
  have hLI' : L ∈ I := hLI ⟨hL.le, le_rfl⟩
  have hFev : ∀ t ∈ I, ∀ z : ℂ, ∀ᶠ q in 𝓝 (t, z), pageMap H U q ∈ energySurface H :=
    fun t ht z => by
      filter_upwards [hO.mem_nhds (show (t, z) ∈ I ×ˢ (Set.univ : Set ℂ) from ⟨ht, trivial⟩)]
        with p hp using hFS p hp
  have hFc : ∀ t ∈ I, ∀ z : ℂ, ContDiffAt ℝ 1 (pageMap H U) (t, z) := fun t ht z =>
    hF.contDiffAt (hO.mem_nhds ⟨ht, trivial⟩)
  have hinj : ∀ t ∈ I, ∀ z : ℂ, Function.Injective (fderiv ℝ (pageMap H U) (t, z)) :=
    fun t ht z => injective_fderiv_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U
      hU t ht z
  have hopen : ∀ t ∈ I, ∀ z : ℂ, ∀ N ∈ 𝓝 (t, z),
      pageMap H U '' N ∈ 𝓝[energySurface H] (pageMap H U (t, z)) := fun t ht z N hN =>
    nhdsWithin_energySurface_le_map (by simp [Module.finrank_prod]) H hH (pageMap H U) (t, z)
      (hFc t ht z) (hFev t ht z) (hinj t ht z) (image_mem_map hN)
  set A := pageMap H U '' (Set.Icc 0 L ×ˢ Set.univ) with hA
  -- leaves at small negative times
  obtain ⟨ε, hε, hεA⟩ : ∃ ε > 0, ∀ s ∈ Set.Ioo (-ε) 0, s ∈ I ∧ ∀ z, pageMap H U (s, z) ∈ A := by
    obtain ⟨z', hz'⟩ := hyL
    have h1 := hleaf 0 h0I L hLI' z' 0 (hz'.trans (hU0 L hLI').symm)
    have h2 : y 0 ∈ Set.range (fun z => pageMap H U (0, z)) := ⟨0, hU0 _ h0I⟩
    rw [h1] at h2
    obtain ⟨z₀, hz₀⟩ := h2
    obtain ⟨c, hc, v, hcv⟩ := isReebPositiveAt_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI
      U hU L hLI' z₀
    have hN : {q : ℝ × ℂ | 0 < q.1} ∈ 𝓝 (L, z₀) :=
      (isOpen_Ioi.preimage continuous_fst).mem_nhds hL
    have hev := (eventually_exists_eq_of_fderiv_eq_reeb H hH (pageMap H U) (L, z₀)
      (hFc L hLI' z₀) (hFev L hLI' z₀) (hinj L hLI' z₀) c hc v hcv y hy 0 hz₀.symm _ hN).2
    have hev2 := hev.and (mem_nhdsWithin_of_mem_nhds (hI.mem_nhds h0I))
    obtain ⟨a, ha, haA⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (show (-1 : ℝ) < 0 by norm_num)).1 hev2
    refine ⟨-a, neg_pos.2 ha, fun s hs => ?_⟩
    rw [neg_neg] at hs
    obtain ⟨⟨⟨q₁, q₂⟩, hq1, hq2, hq3⟩, hsI⟩ := haA hs
    simp only [Set.mem_setOf_eq] at hq1 hq2 hq3
    have hqI : q₁ ∈ Set.Icc 0 L := ⟨hq1.le, hq2.le⟩
    refine ⟨hsI, fun z => ?_⟩
    have h3 := hleaf s hsI q₁ (hLI hqI) 0 q₂ ((hU0 s hsI).trans hq3.symm)
    have h4 : pageMap H U (s, z) ∈ Set.range (fun z => pageMap H U (s, z)) := ⟨z, rfl⟩
    rw [h3] at h4
    obtain ⟨z2, hz2⟩ := h4
    exact ⟨(q₁, z2), ⟨hqI, trivial⟩, hz2⟩
  have hAopen0 : ∀ z, A ∈ 𝓝[energySurface H] (pageMap H U (0, z)) := fun z => by
    have hN : {q : ℝ × ℂ | q.1 ∈ Set.Ioo (-ε) L} ∈ 𝓝 ((0 : ℝ), z) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨neg_lt_zero.2 hε, hL⟩
    refine mem_of_superset (hopen 0 h0I z _ hN) ?_
    rintro _ ⟨⟨s, w⟩, hs, rfl⟩
    simp only [Set.mem_setOf_eq] at hs
    rcases lt_or_ge s 0 with h | h
    · exact (hεA s ⟨hs.1, h⟩).2 w
    · exact ⟨(s, w), ⟨⟨h, hs.2.le⟩, trivial⟩, rfl⟩
  have hAopen : ∀ q ∈ A, A ∈ 𝓝[energySurface H] q := by
    rintro _ ⟨⟨t, z⟩, ⟨ht, -⟩, rfl⟩
    simp only at ht
    rcases ht.1.eq_or_lt with rfl | h0
    · exact hAopen0 z
    rcases ht.2.lt_or_eq with h1 | rfl
    · refine mem_of_superset (hopen t (hLI ht) z _
        ((isOpen_Ioo.preimage continuous_fst).mem_nhds (show t ∈ Set.Ioo 0 L from ⟨h0, h1⟩))) ?_
      rintro _ ⟨⟨s, w⟩, hs, rfl⟩
      exact ⟨(s, w), ⟨Set.Ioo_subset_Icc_self hs, trivial⟩, rfl⟩
    · obtain ⟨z', hz'⟩ := hyL
      have h1 := hleaf 0 h0I t hLI' z' 0 (hz'.trans (hU0 t hLI').symm)
      have h2 : pageMap H U (t, z) ∈ Set.range (fun z => pageMap H U (t, z)) := ⟨z, rfl⟩
      rw [← h1] at h2
      obtain ⟨z2, hz2⟩ := h2
      simp only at hz2
      rw [← hz2]
      exact hAopen0 z2
  have hAS : A ⊆ energySurface H := by
    rintro _ ⟨p, hp, rfl⟩
    exact hFS p ⟨hLI hp.1, trivial⟩
  -- the complement of the orbit is connected
  have hxc : Continuous P.x := continuous_iff_continuousAt.2 fun t => (P.hasDerivAt t).continuousAt
  have hxS : IsReebTrajectory H P.x := ⟨P.mem, P.hasDerivAt⟩
  have hconn : IsPreconnected (energySurface H \ Set.range P.x) :=
    (isPathConnected_energySurface_diff_range le_rfl H hH P.x
      ((hxS.contDiff hH).of_le (by exact_mod_cast le_top)) P.mem).isConnected.isPreconnected
  have hPc : IsCompact (Set.range P.x) := by
    have hper : Function.Periodic P.x P.T := P.periodic
    rw [← hper.image_Icc P.T_pos 0]
    exact isCompact_Icc.image hxc
  -- the open cone over `A`
  let u : Set (V 1) := {q | q ≠ 0 ∧ proj H q ∈ A}
  have hu : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hq0, hqA⟩
    have h1 := hAopen _ hqA
    have h2 : Tendsto (proj H) (𝓝 q) (𝓝[energySurface H] (proj H q)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(contDiffAt_aCoord_proj H hH q hq0).2.continuousAt, ?_⟩
      filter_upwards [isOpen_ne.mem_nhds hq0] with q' hq' using (pfo_proj_mem hH hq')
    filter_upwards [h2 h1, isOpen_ne.mem_nhds hq0] with q' h3 h4 using ⟨h4, h3⟩
  have hcl : closure u ∩ (energySurface H \ Set.range P.x) ⊆ u := by
    rintro q ⟨hqu, hqS, hqP⟩
    have hq0 := pfo_ne_zero hH hqS
    have hqq := pfo_proj_self hH hqS
    obtain ⟨K, hK, hKn, hKP⟩ := exists_compact_subset hPc.isClosed.isOpen_compl hqP
    obtain ⟨r, hr⟩ := exists_norm_le_of_pageMap_mem H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U
      hU 0 L hLI K hK (Set.disjoint_left.2 fun x hx hx' => hKP hx hx')
    have hC : IsCompact (pageMap H U '' (Set.Icc 0 L ×ˢ closedBall (0 : ℂ) r)) :=
      (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
        (hF.continuousOn.mono fun p hp => ⟨hLI hp.1, trivial⟩)
    have hpc : ContinuousAt (proj H) q := (contDiffAt_aCoord_proj H hH q hq0).2.continuousAt
    have hqC : q ∈ closure (pageMap H U '' (Set.Icc 0 L ×ˢ closedBall (0 : ℂ) r)) := by
      rw [mem_closure_iff_nhds]
      intro N hN
      have h1 : proj H ⁻¹' (N ∩ interior K) ∈ 𝓝 q := by
        apply hpc
        rw [hqq]
        exact inter_mem hN (isOpen_interior.mem_nhds hKn)
      obtain ⟨q', ⟨h2, h3⟩, -, ⟨t, z⟩, ⟨ht, -⟩, h4⟩ := mem_closure_iff_nhds.1 hqu _ h1
      refine ⟨proj H q', h2, (t, z), ⟨ht, ?_⟩, h4⟩
      rw [mem_closedBall, dist_zero_right]
      exact hr t ht z (by rw [h4]; exact interior_subset h3)
    rw [hC.isClosed.closure_eq] at hqC
    obtain ⟨p, hp, hpq⟩ := hqC
    exact ⟨hq0, by rw [hqq]; exact ⟨p, ⟨hp.1, trivial⟩, hpq⟩⟩
  have hnonempty : ((energySurface H \ Set.range P.x) ∩ u).Nonempty := by
    have hm := hU.2 0 h0I
    have h1 := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz _ hm.1.1 hm.1.2.1 hm.2 0
    have h2 : pageMap H U (0, 0) ∈ A := ⟨(0, 0), ⟨⟨le_rfl, hL.le⟩, trivial⟩, rfl⟩
    exact ⟨pageMap H U (0, 0), ⟨hAS h2, h1⟩, pfo_ne_zero hH (hAS h2),
      by rw [pfo_proj_self hH (hAS h2)]; exact h2⟩
  intro q hq
  have h := (hconn.subset_of_closure_inter_subset hu hnonempty hcl hq).2
  rwa [pfo_proj_self hH hq.1] at h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (L : ℝ) (hL : 0 < L) (hLI : Set.Icc 0 L ⊆ I)
    (hyL : y L ∈ Set.range (fun z => pageMap H U (0, z))) :
    energySurface H \ Set.range P.x ⊆ pageMap H U '' (Set.Icc 0 L ×ˢ Set.univ) :=
  energySurface_diff_range_subset_image_pageMap_aux H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U hU L hL hLI hyL
