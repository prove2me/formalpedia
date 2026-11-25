-- Prove2me | solution 1 for FiniteEnergyPlane.injOn_pageMap_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:13:05.55731+00:00
-- url     : https://prove2.me/submissions/4280e9d2-10e9-4e43-a2e4-9e60624089b7

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_eventually_exists_eq_of_fderiv_eq_reeb
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_of_pageMap_mem
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
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

theorem injOn_pageMap_Ioo_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (L : ℝ) (hLI : Set.Icc 0 L ⊆ I)
    (hyL : y L ∈ Set.range (fun z => pageMap H U (0, z)))
    (hmin : ∀ t ∈ Set.Ioo 0 L, y t ∉ Set.range (fun z => pageMap H U (0, z))) :
    Set.InjOn (pageMap H U) (Set.Ioo 0 L ×ˢ Set.univ) := by
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
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
  have hleaf : ∀ s ∈ I, ∀ t ∈ I, ∀ z z', pageMap H U (s, z) = pageMap H U (t, z') →
      Set.range (fun z => pageMap H U (s, z)) = Set.range (fun z => pageMap H U (t, z)) :=
    fun s hs t ht z z' h => range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ γ _ _ _ _
      (hU.2 s hs) (hU.2 t ht) z z' h
  rintro ⟨t₀, z₀⟩ ⟨ht₀, -⟩ ⟨t₁, z₁⟩ ⟨ht₁, -⟩ he
  have hsub : Set.Ioo 0 L ⊆ I := Set.Ioo_subset_Icc_self.trans hLI
  have h0I : (0 : ℝ) ∈ I := hLI ⟨le_rfl, (ht₀.1.trans ht₀.2).le⟩
  have hLpos : 0 < L := ht₀.1.trans ht₀.2
  have hLI' : L ∈ I := hLI ⟨hLpos.le, le_rfl⟩
  -- reduce to a claim on the parameters
  suffices key : ∀ t₀ ∈ Set.Ioo 0 L, ∀ t₁ ∈ Set.Ioo 0 L, ∀ z₀ z₁ : ℂ,
      pageMap H U (t₀, z₀) = pageMap H U (t₁, z₁) → ¬ t₀ < t₁ by
    have ht : t₀ = t₁ := le_antisymm (not_lt.1 (key t₁ ht₁ t₀ ht₀ z₁ z₀ he.symm))
      (not_lt.1 (key t₀ ht₀ t₁ ht₁ z₀ z₁ he))
    subst ht
    have hm := hU.2 t₀ (hsub ht₀)
    rw [injective_proj_of_isEmbeddedPlane H hH J hJ P _ hm.1.1 hm.1.2.1 hm.2 he]
  clear he z₀ z₁ ht₀ ht₁ t₀ t₁
  intro t₀ ht₀ t₁ ht₁ z₀ z₁ he hlt
  -- the trajectory avoids the orbit
  have hy0 : y 0 ∉ Set.range P.x := by
    have hm := hU.2 0 h0I
    have := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz _ hm.1.1 hm.1.2.1 hm.2 0
    rwa [show proj H (U (0, 0)) = y 0 from hU0 0 h0I] at this
  have hyP := hy.apply_not_mem_range_of_apply_zero hH P hy0
  obtain ⟨r, hr⟩ := exists_norm_le_of_pageMap_mem H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U hU
    0 L hLI (y '' Set.Icc 0 L) (isCompact_Icc.image hyc)
    (by rw [Set.disjoint_left]; rintro _ ⟨t, -, rfl⟩; exact hyP t)
  -- the relation between times
  let R : Set (ℝ × ℝ) := {p | p ∈ Set.Icc 0 L ×ˢ Set.Icc 0 L ∧ ∃ z, pageMap H U (p.2, z) = y p.1}
  have hR : IsCompact R := by
    let C : Set ((ℝ × ℝ) × ℂ) := (Set.Icc 0 L ×ˢ Set.Icc 0 L) ×ˢ closedBall (0 : ℂ) r
    have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
    have hcont : ContinuousOn (fun p : (ℝ × ℝ) × ℂ => (pageMap H U (p.1.2, p.2), y p.1.1)) C := by
      refine ContinuousOn.prodMk (hF.continuousOn.comp (by fun_prop) ?_) (by fun_prop)
      rintro p ⟨hp, -⟩
      exact ⟨hLI hp.2, trivial⟩
    have hD : IsCompact (C ∩ (fun p : (ℝ × ℝ) × ℂ => (pageMap H U (p.1.2, p.2), y p.1.1)) ⁻¹'
        Set.diagonal (V 1)) :=
      hC.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hC.isClosed isClosed_diagonal)
        Set.inter_subset_left
    have : R = Prod.fst '' (C ∩ (fun p : (ℝ × ℝ) × ℂ =>
        (pageMap H U (p.1.2, p.2), y p.1.1)) ⁻¹' Set.diagonal (V 1)) := by
      ext p
      constructor
      · rintro ⟨hp, z, hz⟩
        refine ⟨(p, z), ⟨⟨hp, ?_⟩, hz⟩, rfl⟩
        rw [mem_closedBall, dist_zero_right]
        exact hr _ hp.2 z (by rw [hz]; exact ⟨_, hp.1, rfl⟩)
      · rintro ⟨⟨p, z⟩, ⟨⟨hp, -⟩, hz⟩, rfl⟩
        exact ⟨hp, z, hz⟩
    rw [this]
    exact hD.image continuous_fst
  -- off the diagonal it is closed
  let Q : Set (ℝ × ℝ) := {p | p ∈ R ∧ t₁ ≤ p.1 ∧ t₀ ≤ p.2 ∧ p.2 < p.1}
  have hQc : IsClosed Q := by
    rw [← closure_subset_iff_isClosed]
    intro p hp
    have hcl : IsClosed (R ∩ {p : ℝ × ℝ | t₁ ≤ p.1 ∧ t₀ ≤ p.2 ∧ p.2 ≤ p.1}) :=
      hR.isClosed.inter ((isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_fst)))
    have hsubQ : Q ⊆ R ∩ {p : ℝ × ℝ | t₁ ≤ p.1 ∧ t₀ ≤ p.2 ∧ p.2 ≤ p.1} := fun q hq =>
      ⟨hq.1, hq.2.1, hq.2.2.1, le_of_lt hq.2.2.2⟩
    have hp' := closure_minimal hsubQ hcl hp
    refine ⟨hp'.1, hp'.2.1, hp'.2.2.1, lt_of_le_of_ne hp'.2.2.2 fun heq => ?_⟩
    obtain ⟨ε, hε, -, hinj⟩ := injOn_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU
      p.1 (hLI hp'.1.1.1)
    have hnb : ball p.1 ε ×ˢ ball p.1 ε ∈ 𝓝 p := by
      have : p = (p.1, p.1) := Prod.ext rfl heq
      rw [this]
      exact prod_mem_nhds (ball_mem_nhds _ hε) (ball_mem_nhds _ hε)
    obtain ⟨q, hq, hqQ⟩ := mem_closure_iff_nhds.1 hp _ hnb
    obtain ⟨⟨hqI, z, hz⟩, -, -, hqlt⟩ := hqQ
    have hz' : pageMap H U (q.2, z) = pageMap H U (q.1, 0) := by
      rw [hz, hU0 _ (hLI hqI.1)]
    have := hinj (show (q.2, z) ∈ ball p.1 ε ×ˢ Set.univ from ⟨hq.2, trivial⟩)
      (show (q.1, (0 : ℂ)) ∈ ball p.1 ε ×ˢ Set.univ from ⟨hq.1, trivial⟩) hz'
    exact hqlt.ne (congrArg Prod.fst this)
  have hQ : IsCompact Q := hR.of_isClosed_subset hQc fun p hp => hp.1
  have hQne : Q.Nonempty := by
    refine ⟨(t₁, t₀), ⟨⟨Set.Ioo_subset_Icc_self ht₁, Set.Ioo_subset_Icc_self ht₀⟩, ?_⟩, le_rfl,
      le_rfl, hlt⟩
    have h1 := hleaf _ (hsub ht₀) _ (hsub ht₁) _ _ he
    have h2 : y t₁ ∈ Set.range (fun z => pageMap H U (t₁, z)) := ⟨0, hU0 _ (hsub ht₁)⟩
    rw [← h1] at h2
    exact h2
  obtain ⟨⟨b, d⟩, ⟨⟨⟨hb, hd⟩, z, hz⟩, hb1, hd0, hdb⟩, hmax⟩ :=
    hQ.exists_isMaxOn hQne continuous_fst.continuousOn
  simp only at hb hd hz hb1 hd0 hdb
  have hd0' : 0 < d := ht₀.1.trans_le hd0
  rcases hb.2.lt_or_eq with hbL | rfl
  · -- continue the relation beyond `b`
    obtain ⟨c, hc, v, hcv⟩ := isReebPositiveAt_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI
      U hU d (hLI hd) z
    have hN : {q : ℝ × ℂ | q.1 < b} ∈ 𝓝 (d, z) :=
      (isOpen_Iio.preimage continuous_fst).mem_nhds hdb
    have hev := (eventually_exists_eq_of_fderiv_eq_reeb H hH (pageMap H U) (d, z)
      (hF.contDiffAt (hO.mem_nhds ⟨hLI hd, trivial⟩))
      (by filter_upwards [hO.mem_nhds (show (d, z) ∈ I ×ˢ (Set.univ : Set ℂ) from
            ⟨hLI hd, trivial⟩)] with p hp using hFS p hp)
      (injective_fderiv_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU d
        (hLI hd) z) c hc v hcv y hy b hz.symm _ hN).1
    obtain ⟨s, ⟨⟨q₁, q₂⟩, hq1, hq2, hq3⟩, hs⟩ := (hev.and (Ioo_mem_nhdsGT hbL)).exists
    simp only [Set.mem_setOf_eq] at hq1 hq2 hq3
    have hmem : (s, q₁) ∈ Q := by
      refine ⟨⟨⟨⟨by linarith [hb.1, hs.1], hs.2.le⟩, ⟨by linarith, by linarith [hs.1, hs.2]⟩⟩,
        q₂, hq3⟩, ?_, ?_, ?_⟩
      · show t₁ ≤ s; linarith [hs.1]
      · show t₀ ≤ q₁; linarith
      · show q₁ < s; linarith [hs.1]
    have : s ≤ b := hmax hmem
    linarith [hs.1]
  · obtain ⟨z', hz'⟩ := hyL
    have h1 := hleaf _ (hLI hd) _ h0I z z' (hz.trans hz'.symm)
    have h2 : y d ∈ Set.range (fun z => pageMap H U (d, z)) := ⟨0, hU0 _ (hLI hd)⟩
    rw [h1] at h2
    exact hmin d ⟨hd0', hdb⟩ h2

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
    (hU : IsPageFamilyOn H J P γ y l I U) (L : ℝ) (hLI : Set.Icc 0 L ⊆ I)
    (hyL : y L ∈ Set.range (fun z => pageMap H U (0, z)))
    (hmin : ∀ t ∈ Set.Ioo 0 L, y t ∉ Set.range (fun z => pageMap H U (0, z))) :
    Set.InjOn (pageMap H U) (Set.Ioo 0 L ×ˢ Set.univ) :=
  injOn_pageMap_Ioo_aux H hH J hJ P hcz γ hγ hγT hΛ y hy l hl I hI U hU L hLI hyL hmin
