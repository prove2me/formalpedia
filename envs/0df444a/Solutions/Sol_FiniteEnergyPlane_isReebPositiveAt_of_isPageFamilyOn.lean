-- Prove2me | solution 1 for FiniteEnergyPlane.isReebPositiveAt_of_isPageFamilyOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:25:43.18932+00:00
-- url     : https://prove2.me/submissions/c4b418d9-4092-47a5-855f-df581fbd5bd2

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_continuousAt_reeb
import Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_reeb_spec



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

theorem isReebPositiveAt_of_isPageFamilyOn_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t : ℝ) (ht : t ∈ I) (z : ℂ) :
    IsReebPositiveAt H U (t, z) := by
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hU1 : ContDiffOn ℝ 1 U (I ×ˢ Set.univ) := hU.1.of_le (by exact_mod_cast hl)
  have hO : IsOpen (I ×ˢ (Set.univ : Set ℂ)) := hI.prod isOpen_univ
  have hF := contDiffOn_pageMap H hH U I hI hU1 hne
  set F := pageMap H U with hFdef
  have hFc : ∀ z, ContDiffAt ℝ 1 F (t, z) := fun z => hF.contDiffAt (hO.mem_nhds ⟨ht, trivial⟩)
  have hFS : ∀ z, ∀ᶠ q in 𝓝 (t, z), F q ∈ energySurface H := fun z => by
    filter_upwards [hO.mem_nhds (show (t, z) ∈ I ×ˢ (Set.univ : Set ℂ) from ⟨ht, trivial⟩)] with q hq
    exact (pfo_proj_mem hH (hne q hq))
  have hinj : ∀ z, Function.Injective (fderiv ℝ F (t, z)) := fun z =>
    injective_fderiv_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U hU t ht z
  have key := fun z => (exists_equiv_hasStrictFDerivAt_exp_smul_of_injective (by simp [Module.finrank_prod]) H hH F (t, z) (hFc z) (hFS z)
    (hinj z))
  choose h0 L hL hLs using key
  -- the coefficients of the Reeb vector
  let X : ℂ → ℝ × ℝ × ℂ := fun z => (L z).symm (reeb H (F (t, z)))
  have hX : ∀ z, (X z).1 • F (t, z) + fderiv ℝ F (t, z) (X z).2 = reeb H (F (t, z)) := fun z => by
    rw [← hL]; exact (L z).apply_symm_apply _
  have hSz : ∀ z, F (t, z) ∈ energySurface H := fun z => (hFS z).self_of_nhds
  have hX1 : ∀ z, (X z).1 = 0 := fun z => by
    have h1 := congrArg (fderiv ℝ H (F (t, z))) (hX z)
    rw [map_add, map_smul, h0, add_zero, smul_eq_mul, (reeb_spec H hH _ (hSz z)).2.2.1] at h1
    exact (mul_eq_zero.1 h1).resolve_right (hH.2.2 _ (hSz z)).ne'
  have hXR : ∀ z, fderiv ℝ F (t, z) (X z).2 = reeb H (F (t, z)) := fun z => by
    have := hX z
    rwa [hX1, zero_smul, zero_add] at this
  have hc0 : ∀ z, (X z).2.1 ≠ 0 := by
    intro z hz
    have hsl : HasFDerivAt (fun w => F (t, w))
        ((fderiv ℝ F (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) z :=
      HasFDerivAt.comp z (g := F) ((hFc z).differentiableAt (by norm_num)).hasFDerivAt
        (hasFDerivAt_prodMk_right t z)
    have h1 : fderiv ℝ (fun w => F (t, w)) z (X z).2.2 = reeb H (F (t, z)) := by
      rw [hsl.fderiv, ← hXR z, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      rw [← hz]
    have hR : reeb H (F (t, z)) ≠ 0 := by
      intro h
      have := (reeb_spec H hH _ (hSz z)).2.1
      rw [h] at this
      simp [liouville, omega0, dot] at this
    have hv : (X z).2.2 ≠ 0 := fun hv => hR (by rw [← h1, hv, map_zero])
    exact isFastPlane_immersion_transverse H hH J hJ _ (hU.2 t ht).1.1 z _ hv 1
      (by rw [one_smul]; exact h1)
  have hXc : Continuous X := by
    rw [continuous_iff_continuousAt]
    intro z
    let Λ : ℂ → (ℝ × ℝ × ℂ) →L[ℝ] V 1 := fun z => (L z : (ℝ × ℝ × ℂ) →L[ℝ] V 1)
    have hΛ : ∀ z, Λ z = (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).smulRight (F (t, z)) +
        (fderiv ℝ F (t, z)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) := fun z =>
      ContinuousLinearMap.ext fun q => hL z q
    have hi : ContinuousAt (fun z : ℂ => (t, z)) z := by fun_prop
    have hFz : ContinuousAt (fun z => F (t, z)) z := ContinuousAt.comp' (hFc z).continuousAt hi
    have hDz : ContinuousAt (fun z => fderiv ℝ F (t, z)) z :=
      ContinuousAt.comp' (f := fun z : ℂ => (t, z))
        (((hFc z).fderiv_right (m := 0) (by norm_num)).continuousAt) hi
    have hΛc : ContinuousAt Λ z := by
      have : Λ = fun z => (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ × ℂ) (V 1)
          (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))) (F (t, z)) +
        ((ContinuousLinearMap.compL ℝ (ℝ × ℝ × ℂ) (ℝ × ℂ) (V 1)).flip
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))) (fderiv ℝ F (t, z)) := by
        funext z; rw [hΛ]; rfl
      rw [this]
      exact ((ContinuousLinearMap.continuous _).continuousAt.comp' hFz).add
        ((ContinuousLinearMap.continuous _).continuousAt.comp' hDz)
    have hinv : ContinuousAt (fun z => ContinuousLinearMap.inverse (Λ z)) z :=
      ContinuousAt.comp' (f := Λ) (contDiffAt_map_inverse (𝕜 := ℝ) (n := 0) (L z)).continuousAt hΛc
    have hR : ContinuousAt (fun z => reeb H (F (t, z))) z :=
      ContinuousAt.comp' (continuousAt_reeb H hH _ (hSz z)) hFz
    have : X = fun z => ContinuousLinearMap.inverse (Λ z) (reeb H (F (t, z))) := by
      funext z
      show _ = ContinuousLinearMap.inverse (L z : (ℝ × ℝ × ℂ) →L[ℝ] V 1) _
      rw [ContinuousLinearMap.inverse_equiv]; rfl
    rw [this]
    exact hinv.clm_apply hR
  -- at the base point
  have hbase : (X 0).2.1 = 1 := by
    have h1 : HasDerivAt (fun s => F (s, (0 : ℂ))) (fderiv ℝ F (t, 0) (1, 0)) t := by
      have h2 : HasDerivAt (fun s : ℝ => (s, (0 : ℂ))) ((1 : ℝ), (0 : ℂ)) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t _)
      exact HasFDerivAt.comp_hasDerivAt t (l := F)
        ((hFc 0).differentiableAt (by norm_num)).hasFDerivAt h2
    have hFy : ∀ s ∈ I, F (s, 0) = y s := fun s hs => by
      have h : U (s, 0) = y s := (hU.2 s hs).1.2.2.1
      show proj H (U (s, 0)) = y s
      rw [h, pfo_proj_self hH (hy.1 s)]
    have h2 : HasDerivAt (fun s => F (s, (0 : ℂ))) (reeb H (y t)) t :=
      (hy.2 t).congr_of_eventuallyEq (by filter_upwards [hI.mem_nhds ht] with s hs using hFy s hs)
    have h3 : fderiv ℝ F (t, 0) (1, 0) = fderiv ℝ F (t, 0) (X 0).2 := by
      rw [hXR, hFy t ht]; exact h1.unique h2
    rw [← hinj 0 h3]
  refine ⟨(X z).2.1, ?_, (X z).2.2, hXR z⟩
  by_contra hneg
  have hcc : Continuous fun z => (X z).2.1 := continuous_fst.comp (continuous_snd.comp hXc)
  obtain ⟨w, hw⟩ := mem_range_of_exists_le_of_exists_ge hcc ⟨z, not_lt.1 hneg⟩
    ⟨0, by rw [hbase]; exact zero_le_one⟩
  exact hc0 w hw

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t : ℝ) (ht : t ∈ I) (z : ℂ) :
    IsReebPositiveAt H U (t, z) :=
  isReebPositiveAt_of_isPageFamilyOn_aux H hH J hJ P hcz γ y hy l hl I hI U hU t ht z
