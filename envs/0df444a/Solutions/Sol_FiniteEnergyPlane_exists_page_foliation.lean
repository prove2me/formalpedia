-- Prove2me | solution 1 for FiniteEnergyPlane.exists_page_foliation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:44:17.992224+00:00
-- url     : https://prove2.me/submissions/e542d1d9-a848-472d-ba05-99c1bc482fa7

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_energySurface_diff_range_subset_image_pageMap
import Theorems.Thm_FiniteEnergyPlane_exists_page_family_along_trajectory
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_Ioo
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_isBounded_preimage_proj_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_isReebPositiveAt_of_isPageFamilyOn
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

theorem exists_page_foliation_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (τ : ℝ) (hτ : 0 < τ)
    (hret : y τ ∈ Set.range (fun z => proj H (v z))) (l : ℕ) (hl : 1 ≤ l) :
    ∃ L > 0, ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFoliation H J P γ y l L δ U ∧
      ∀ z, U (0, z) = v z := by
  obtain ⟨δ₀, hδ₀, U, hU, hUv⟩ := exists_page_family_along_trajectory H hH J hJ P hcz γ hΛ y hy v hv
    l hl (τ + 1) (by linarith)
  set I := Set.Ioo (-δ₀) (τ + 1) with hIdef
  have hI : IsOpen I := isOpen_Ioo
  have h0I : (0 : ℝ) ∈ I := ⟨neg_lt_zero.2 hδ₀, by linarith⟩
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hFS : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), pageMap H U p ∈ energySurface H := fun p hp =>
    (pfo_proj_mem hH (hne p hp))
  have hU0 : ∀ t ∈ I, pageMap H U (t, 0) = y t := fun t ht => by
    show proj H (U (t, 0)) = _
    rw [show U (t, 0) = y t from (hU.2 t ht).1.2.2.1, pfo_proj_self hH (hy.1 t)]
  have hleaf : ∀ s ∈ I, ∀ t ∈ I, ∀ z z', pageMap H U (s, z) = pageMap H U (t, z') →
      Set.range (fun z => pageMap H U (s, z)) = Set.range (fun z => pageMap H U (t, z)) :=
    fun s hs t ht z z' h => range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ γ _ _ _ _
      (hU.2 s hs) (hU.2 t ht) z z' h
  have hmiss : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), pageMap H U p ∉ Set.range P.x := fun p hp => by
    have hm := hU.2 p.1 hp.1
    exact proj_not_mem_range_of_isFastPlane H hH J hJ P hcz _ hm.1.1 hm.1.2.1 hm.2 p.2
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
  have hyP := hy.apply_not_mem_range_of_apply_zero hH P
    (by rw [← hU0 0 h0I]; exact hmiss _ ⟨h0I, trivial⟩)
  have hret' : y τ ∈ Set.range (fun z => pageMap H U (0, z)) := by
    obtain ⟨z, hz⟩ := hret
    exact ⟨z, by rw [← hz]; show proj H (U (0, z)) = _; rw [hUv]⟩
  -- the first return
  obtain ⟨ε, hε, -, hεi⟩ := injOn_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU 0 h0I
  let E : Set ℝ := {t | t ∈ Set.Icc 0 τ ∧ ε ≤ t ∧ y t ∈ Set.range (fun z => pageMap H U (0, z))}
  have hsmall : ∀ t ∈ I, 0 < t → y t ∈ Set.range (fun z => pageMap H U (0, z)) → ε ≤ t := by
    rintro t ht h0 ⟨z, hz⟩
    by_contra hlt
    have := hεi (show ((0 : ℝ), z) ∈ ball 0 ε ×ˢ Set.univ from ⟨mem_ball_self hε, trivial⟩)
      (show (t, (0 : ℂ)) ∈ ball (0 : ℝ) ε ×ˢ Set.univ from
        ⟨by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos h0]; exact not_le.1 hlt, trivial⟩)
      (hz.trans (hU0 t ht).symm)
    exact h0.ne (congrArg Prod.fst this)
  have hEc : IsCompact E := by
    have hm := hU.2 0 h0I
    have hK : IsCompact (y '' Set.Icc 0 τ) := isCompact_Icc.image hyc
    have hb := isBounded_preimage_proj_of_isNondegenerateEnd H hH P _ hm.1.2.1 _ hK
      (by rw [Set.disjoint_left]; rintro _ ⟨t, -, rfl⟩; exact hyP t)
    obtain ⟨r, hr⟩ := hb.subset_closedBall 0
    have hcont : Continuous (fun z => pageMap H U (0, z)) := by
      have hF := contDiffOn_pageMap H hH U I hI (hU.1.of_le (by exact_mod_cast hl)) hne
      rw [← continuousOn_univ]
      exact hF.continuousOn.comp (by fun_prop) fun z _ => ⟨h0I, trivial⟩
    have hC : IsClosed ((fun z => pageMap H U (0, z)) '' closedBall (0 : ℂ) r) :=
      ((isCompact_closedBall _ _).image hcont).isClosed
    have : E = Set.Icc 0 τ ∩ (Set.Ici ε ∩
        y ⁻¹' ((fun z => pageMap H U (0, z)) '' closedBall (0 : ℂ) r)) := by
      ext t
      constructor
      · rintro ⟨h1, h2, z, hz⟩
        have h3 : proj H (U (0, z)) ∈ y '' Set.Icc 0 τ := ⟨t, h1, hz.symm⟩
        exact ⟨h1, h2, z, hr h3, hz⟩
      · rintro ⟨h1, h2, z, -, hz⟩
        exact ⟨h1, h2, z, hz⟩
    rw [this]
    exact isCompact_Icc.inter_right (isClosed_Ici.inter (hC.preimage hyc))
  have hτI : τ ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨L, ⟨hLτ, hεL, hyL⟩, hLmin⟩ := hEc.exists_isLeast
    ⟨τ, ⟨hτ.le, le_rfl⟩, hsmall τ hτI hτ hret', hret'⟩
  have hL : 0 < L := hε.trans_le hεL
  have hLI : Set.Icc 0 L ⊆ I := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, hLτ.2]⟩
  have hLI' : L ∈ I := hLI ⟨hL.le, le_rfl⟩
  have hmin : ∀ t ∈ Set.Ioo 0 L, y t ∉ Set.range (fun z => pageMap H U (0, z)) := fun t ht h => by
    have := hLmin ⟨⟨ht.1.le, by linarith [ht.2, hLτ.2]⟩,
      hsmall t (hLI (Set.Ioo_subset_Icc_self ht)) ht.1 h, h⟩
    linarith [ht.2]
  have hL0 : Set.range (fun z => pageMap H U (L, z)) = Set.range (fun z => pageMap H U (0, z)) := by
    obtain ⟨z', hz'⟩ := hyL
    exact hleaf L hLI' 0 h0I 0 z' ((hU0 L hLI').trans hz'.symm)
  refine ⟨L, hL, min δ₀ 1, lt_min hδ₀ one_pos, U, ⟨?_, ?_, hL0, ?_, ?_, ?_⟩, hUv⟩
  · have hs : Set.Ioo (-min δ₀ 1) (L + min δ₀ 1) ⊆ I := fun t ht =>
      ⟨by linarith [ht.1, min_le_left δ₀ 1], by linarith [ht.2, min_le_right δ₀ 1, hLτ.2]⟩
    exact ⟨hU.1.mono (Set.prod_mono hs subset_rfl), fun t ht => hU.2 t (hs ht)⟩
  · rintro ⟨t, z⟩ ⟨ht, -⟩
    have htI : t ∈ I :=
      ⟨by linarith [ht.1, min_le_left δ₀ 1], by linarith [ht.2, min_le_right δ₀ 1, hLτ.2]⟩
    exact ⟨hmiss _ ⟨htI, trivial⟩,
      injective_fderiv_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU t htI z,
      isReebPositiveAt_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU t htI z⟩
  · rintro ⟨t, z⟩ ⟨ht, -⟩
    have htI : t ∈ I := hLI (Set.Ioo_subset_Icc_self ht)
    refine ⟨hFS _ ⟨htI, trivial⟩, ?_⟩
    rintro (⟨z', hz'⟩ | h)
    · have h1 := hleaf t htI 0 h0I z z' hz'.symm
      have h2 : y t ∈ Set.range (fun z => pageMap H U (t, z)) := ⟨0, hU0 t htI⟩
      rw [h1] at h2
      exact hmin t ht h2
    · exact hmiss _ ⟨htI, trivial⟩ h
  · exact injOn_pageMap_Ioo H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U hU L hLI hyL hmin
  · rintro q ⟨hqS, hq⟩
    rw [Set.mem_union, not_or] at hq
    obtain ⟨⟨t, z⟩, ⟨ht, -⟩, hpq⟩ := energySurface_diff_range_subset_image_pageMap H hH J hJ P hcz
      γ hγ hγT hΛ y hy l hl I hI U hU L hL hLI hyL ⟨hqS, hq.2⟩
    simp only at ht
    refine ⟨(t, z), ⟨⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, trivial⟩, hpq⟩
    · rintro rfl
      exact hq.1 ⟨z, hpq⟩
    · rintro rfl
      exact hq.1 (hL0 ▸ ⟨z, hpq⟩)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (τ : ℝ) (hτ : 0 < τ)
    (hret : y τ ∈ Set.range (fun z => proj H (v z))) (l : ℕ) (hl : 1 ≤ l) :
    ∃ L > 0, ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFoliation H J P γ y l L δ U ∧
      ∀ z, U (0, z) = v z :=
  exists_page_foliation_aux H hH J hJ P hcz γ hγ (hγ₁ P le_rfl) hΛ y hy v hv τ hτ hret l hl
