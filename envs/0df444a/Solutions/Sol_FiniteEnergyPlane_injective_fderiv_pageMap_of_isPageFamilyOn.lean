-- Prove2me | solution 1 for FiniteEnergyPlane.injective_fderiv_pageMap_of_isPageFamilyOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:58:38.062282+00:00
-- url     : https://prove2.me/submissions/b8ac54eb-27d8-480d-895c-1132d23f7fd5

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_exists_contDiff_rotation_gauge
import Theorems.Thm_FiniteEnergyPlane_exists_local_page_family



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

theorem injective_fderiv_pageMap_of_isPageFamilyOn_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t : ℝ) (ht : t ∈ I) (z : ℂ) :
    Function.Injective (fderiv ℝ (pageMap H U) (t, z)) := by
  obtain ⟨ε, hε, W, hW, -, -, hWi, -⟩ :=
    exists_local_page_family H hH J hJ P hcz γ y hy t _ (hU.2 t ht) l hl
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.1 hI t ht
  have hU' : IsPageFamilyOn H J P γ y l (ball t r) U :=
    ⟨hU.1.mono (Set.prod_mono hrI subset_rfl), fun s hs => hU.2 s (hrI hs)⟩
  obtain ⟨θ, hθ, hθU⟩ := exists_contDiff_rotation_gauge H hH J hJ P hcz γ y hy l hl
    (ball t r) (ball t ε) isOpen_ball isOpen_ball (convex_ball _ _) (convex_ball _ _) U W hU' hW
  have hB : IsOpen (ball t r ∩ ball t ε) := isOpen_ball.inter isOpen_ball
  have htB : t ∈ ball t r ∩ ball t ε := ⟨mem_ball_self hr, mem_ball_self hε⟩
  let E : ℝ → ℂ := fun t => Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I)
  have hEd : DifferentiableAt ℝ E t := by
    have h1 : DifferentiableAt ℝ θ t :=
      (hθ.contDiffAt (hB.mem_nhds htB)).differentiableAt (by exact_mod_cast (by omega : l ≠ 0))
    have h3 : DifferentiableAt ℝ (fun t => ((2 * π * θ t : ℝ) : ℂ)) t :=
      Complex.ofRealCLM.differentiableAt.comp t (h1.const_mul (2 * π))
    exact (h3.mul_const Complex.I).cexp
  let g : ℝ × ℂ → ℝ × ℂ := fun p => (p.1, E p.1 * p.2)
  let g' : ℝ × ℂ →L[ℝ] ℝ × ℂ := (ContinuousLinearMap.fst ℝ ℝ ℂ).prod
    (E t • ContinuousLinearMap.snd ℝ ℝ ℂ +
      z • ((fderiv ℝ E t).comp (ContinuousLinearMap.fst ℝ ℝ ℂ)))
  have hg : HasFDerivAt g g' (t, z) := by
    have h1 : HasFDerivAt (fun p : ℝ × ℂ => E p.1) _ (t, z) :=
      HasFDerivAt.comp (t, z) (g := E) hEd.hasFDerivAt hasFDerivAt_fst
    exact hasFDerivAt_fst.prodMk (h1.mul hasFDerivAt_snd)
  have hW1 : ContDiffOn ℝ 1 W (ball t ε ×ˢ Set.univ) := hW.1.of_le (by exact_mod_cast hl)
  have hWne : ∀ p ∈ ball t ε ×ˢ (Set.univ : Set ℂ), W p ≠ 0 := fun p hp =>
    (hW.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hgm : g (t, z) ∈ ball t ε ×ˢ (Set.univ : Set ℂ) := ⟨htB.2, trivial⟩
  have hWd : HasFDerivAt (pageMap H W) (fderiv ℝ (pageMap H W) (g (t, z))) (g (t, z)) :=
    (((contDiffOn_pageMap H hH W _ isOpen_ball hW1 hWne).contDiffAt
      ((isOpen_ball.prod isOpen_univ).mem_nhds hgm)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (pageMap H U) ((fderiv ℝ (pageMap H W) (g (t, z))).comp g') (t, z) := by
    refine (hWd.comp (t, z) hg).congr_of_eventuallyEq ?_
    filter_upwards [(hB.prod isOpen_univ).mem_nhds
      (show (t, z) ∈ (ball t r ∩ ball t ε) ×ˢ (Set.univ : Set ℂ) from ⟨htB, trivial⟩)] with p hp
    exact congrArg (proj H) (hθU p.1 hp.1 p.2)
  rw [hcomp.fderiv]
  refine (hWi _ hgm).1.comp ?_
  rw [injective_iff_map_eq_zero]
  rintro ⟨c, v⟩ h
  have h1 : c = 0 := congrArg Prod.fst h
  subst h1
  have h2 : E t * v + z * fderiv ℝ E t 0 = 0 := congrArg Prod.snd h
  rw [map_zero, mul_zero, add_zero] at h2
  rw [(mul_eq_zero.1 h2).resolve_left (Complex.exp_ne_zero _)]
  rfl

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
    Function.Injective (fderiv ℝ (pageMap H U) (t, z)) :=
  injective_fderiv_pageMap_of_isPageFamilyOn_aux H hH J hJ P hcz γ y hy l hl I hI U hU t ht z
