-- Prove2me | solution 1 for FiniteEnergyPlane.exists_pos_le_leaf_speed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T15:43:14.568681+00:00
-- url     : https://prove2.me/submissions/dbe4bfd9-f708-4d17-b8f3-7aee328e8a43

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_continuousAt_reeb



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_pos_le_leaf_speed_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (U : ℝ × ℂ → V 1) (hU : ContDiff ℝ 1 U) (hne : ∀ p, U p ≠ 0)
    (hinj : ∀ p, Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p, IsReebPositiveAt H U p)
    (K : Set (V 1)) (hK : IsCompact K) (hKU : K ⊆ Set.range (pageMap H U)) :
    ∃ ε > 0, ∀ y : ℝ → V 1, IsReebTrajectory H y → ∀ t, y t ∈ K →
      ∃ (f : ℝ → ℝ) (d : ℝ), ε ≤ d ∧ HasDerivAt f d t ∧
        ∀ᶠ s in 𝓝 t, y s ∈ Set.range (fun z => pageMap H U (f s, z)) := by
  have hloc : ∀ p : ℝ × ℂ,
      ∃ N ∈ 𝓝 (pageMap H U p), ∃ ε > 0, ∀ y : ℝ → V 1, IsReebTrajectory H y → ∀ t, y t ∈ N →
        ∃ (f : ℝ → ℝ) (d : ℝ), ε ≤ d ∧ HasDerivAt f d t ∧
          ∀ᶠ s in 𝓝 t, y s ∈ Set.range (fun z => pageMap H U (f s, z)) := by
    intro p
    have hFS : ∀ q, pageMap H U q ∈ energySurface H := fun q => proj_mem_energySurface H hH _ (hne q)
    have hF : ContDiffAt ℝ 1 (pageMap H U) p := by
      have := contDiffOn_pageMap H hH U Set.univ isOpen_univ hU.contDiffOn (fun q _ => hne q)
      rw [Set.univ_prod_univ, contDiffOn_univ] at this
      exact this.contDiffAt
    obtain ⟨-, L, hL, hs⟩ := exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
      (by simp [Module.finrank_prod]) H hH _ p hF (.of_forall hFS) (hinj p)
    obtain ⟨c, hc, v, hcv⟩ := hpos p
    have hGc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℂ => Real.exp q.1 • pageMap H U q.2) ((0 : ℝ), p) :=
      (Real.contDiff_exp.contDiffAt.comp _ contDiffAt_fst).smul
        (ContDiffAt.comp (g := pageMap H U) _ hF contDiffAt_snd)
    set G : ℝ × ℝ × ℂ → V 1 := fun q => Real.exp q.1 • pageMap H U q.2 with hGdef
    have hGp : G ((0 : ℝ), p) = pageMap H U p := by simp [hGdef]
    have hgC := hGc.to_localInverse hs.hasFDerivAt one_ne_zero
    rw [hGp] at hgC
    let g := hs.localInverse G L _
    have hgC : ContDiffAt ℝ 1 g (pageMap H U p) := hgC
    have hg : HasFDerivAt g (L.symm : V 1 →L[ℝ] ℝ × ℝ × ℂ) (pageMap H U p) := by
      have := hs.to_localInverse.hasFDerivAt; rwa [hGp] at this
    have hGg : ∀ᶠ q in 𝓝 (pageMap H U p), G (g q) = q := by
      have := hs.eventually_right_inverse; rwa [hGp] at this
    let pr : (ℝ × ℝ × ℂ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))
    have hcont : ContinuousAt (fun x => pr (fderiv ℝ g x (reeb H x))) (pageMap H U p) :=
      pr.continuous.continuousAt.comp
        ((hgC.continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_reeb H hH _ (hFS p)))
    have hval : pr (fderiv ℝ g (pageMap H U p) (reeb H (pageMap H U p))) = c := by
      rw [hg.fderiv]
      have : L.symm (reeb H (pageMap H U p)) = ((0 : ℝ), (c, v)) := by
        rw [ContinuousLinearEquiv.symm_apply_eq, hL]; simp [hcv]
      show pr (L.symm _) = c
      rw [this]; rfl
    have h1 : ∀ᶠ x in 𝓝 (pageMap H U p), c / 2 < pr (fderiv ℝ g x (reeb H x)) :=
      hcont.eventually (lt_mem_nhds (by simp only [hval]; linarith))
    have h2 : ∀ᶠ x in 𝓝 (pageMap H U p), DifferentiableAt ℝ g x :=
      (hgC.eventually (by simp)).mono fun x hx => hx.differentiableAt one_ne_zero
    refine ⟨_, h1.and (h2.and hGg.eventually_nhds), c / 2, by linarith, fun y hy t ht => ?_⟩
    obtain ⟨ht1, ht2, ht3⟩ := ht
    refine ⟨fun s => pr (g (y s)), _, ht1.le,
      pr.hasFDerivAt.comp_hasDerivAt t (ht2.hasFDerivAt.comp_hasDerivAt t (hy.2 t)), ?_⟩
    filter_upwards [(hy.2 t).continuousAt.eventually ht3] with s hs'
    refine ⟨(g (y s)).2.2, ?_⟩
    have e1 := proj_smul_eq_of_mem_energySurface H hH _ (hFS (g (y s)).2) _ (Real.exp_pos (g (y s)).1)
    have e2 := proj_smul_eq_of_mem_energySurface H hH _ (hy.1 s) 1 one_pos
    have hs'' : Real.exp (g (y s)).1 • pageMap H U (g (y s)).2 = y s := hs'
    rw [hs''] at e1
    rw [one_smul] at e2
    exact e1.symm.trans e2
  refine hK.induction_on (p := fun K => ∃ ε > 0, ∀ y : ℝ → V 1, IsReebTrajectory H y → ∀ t,
      y t ∈ K → ∃ (f : ℝ → ℝ) (d : ℝ), ε ≤ d ∧ HasDerivAt f d t ∧
        ∀ᶠ s in 𝓝 t, y s ∈ Set.range (fun z => pageMap H U (f s, z))) ?_ ?_ ?_ ?_
  · exact ⟨1, one_pos, fun y _ t h => h.elim⟩
  · rintro A B hAB ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun y hy t ht => h y hy t (hAB ht)⟩
  · rintro A B ⟨ε, hε, h⟩ ⟨ε', hε', h'⟩
    refine ⟨min ε ε', lt_min hε hε', fun y hy t ht => ?_⟩
    rcases ht with ht | ht
    · obtain ⟨f, d, hd, h⟩ := h y hy t ht
      exact ⟨f, d, (min_le_left _ _).trans hd, h⟩
    · obtain ⟨f, d, hd, h⟩ := h' y hy t ht
      exact ⟨f, d, (min_le_right _ _).trans hd, h⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := hKU hx
    obtain ⟨N, hN, h⟩ := hloc p
    exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, h⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (U : ℝ × ℂ → V 1) (hU : ContDiff ℝ 1 U) (hne : ∀ p, U p ≠ 0)
    (hinj : ∀ p, Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p, IsReebPositiveAt H U p)
    (K : Set (V 1)) (hK : IsCompact K) (hKU : K ⊆ Set.range (pageMap H U)) :
    ∃ ε > 0, ∀ y : ℝ → V 1, IsReebTrajectory H y → ∀ t, y t ∈ K →
      ∃ (f : ℝ → ℝ) (d : ℝ), ε ≤ d ∧ HasDerivAt f d t ∧
        ∀ᶠ s in 𝓝 t, y s ∈ Set.range (fun z => pageMap H U (f s, z)) :=
  exists_pos_le_leaf_speed_aux H hH U hU hne hinj hpos K hK hKU
