-- Prove2me | solution 1 for FiniteEnergyPlane.isEmbeddedPlane_of_isCylCloseTo
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:52:18.396204+00:00
-- url     : https://prove2.me/submissions/83aba175-d318-4f33-93bf-cf285fc590ed

import Definitions.Def_FiniteEnergyPlane_CylClose
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_injective_of_weighted_lower_bound
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_aCoord_proj_comp_iff



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff Real

theorem isEmbeddedPlane_of_isCylCloseTo_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ 1 f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      IsEmbeddedPlane f := by
  obtain ⟨c, hc, hK⟩ := exists_mul_norm_sub_le_of_isEmbeddedPlane H hH J hJ P u hu huP hue
  obtain ⟨ε, hε, hT⟩ := exists_injective_of_weighted_lower_bound (E := ℝ × V 1) (c / 2) (by positivity)
  refine ⟨ε, hε, fun f hf hf0 hclose => ?_⟩
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z (Set.mem_univ z)
  have hus : Differentiable ℝ u :=
    (contDiffOn_univ.1 hu.1.1).differentiable (by simp)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- coordinate maps
  have hcoord : ∀ (g : ℂ → V 1), Differentiable ℝ g → (∀ z, g z ≠ 0) → ∀ z,
      DifferentiableAt ℝ (fun w => aCoord H (g w)) z ∧
        DifferentiableAt ℝ (fun w => proj H (g w)) z := by
    intro g hg hg0 z
    obtain ⟨ha, hp⟩ := contDiffAt_aCoord_proj H hH (g z) (hg0 z)
    exact ⟨(ha.differentiableAt (by simp)).comp z (hg z),
      (hp.differentiableAt (by simp)).comp z (hg z)⟩
  have hprod : ∀ (g : ℂ → V 1), Differentiable ℝ g → (∀ z, g z ≠ 0) → ∀ z,
      HasFDerivAt (fun w => (aCoord H (g w), proj H (g w)))
        ((fderiv ℝ (fun w => aCoord H (g w)) z).prod (fderiv ℝ (fun w => proj H (g w)) z)) z :=
    fun g hg hg0 z =>
      (hcoord g hg hg0 z).1.hasFDerivAt.prodMk (hcoord g hg hg0 z).2.hasFDerivAt
  obtain ⟨hinj, hdinj⟩ := hT (fun w => (aCoord H (f w), proj H (f w)))
    (fun w => (aCoord H (u w), proj H (u w)))
    (fun z => (hprod f hfd hf0 z).differentiableAt)
    (fun z => (hprod u hus hu0 z).differentiableAt)
    (fun z z' => by
      have h1 := hK z z'
      have hS : 0 < 1 + ‖z‖ + ‖z'‖ := by positivity
      have h2 : |aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖ ≤
          2 * ‖((aCoord H (u z), proj H (u z)) : ℝ × V 1) - (aCoord H (u z'), proj H (u z'))‖ := by
        have ha := norm_fst_le (((aCoord H (u z), proj H (u z)) : ℝ × V 1) -
          (aCoord H (u z'), proj H (u z')))
        have hb := norm_snd_le (((aCoord H (u z), proj H (u z)) : ℝ × V 1) -
          (aCoord H (u z'), proj H (u z')))
        simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] at ha hb
        linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hS.le
      have h4 : c / 2 * ‖z - z'‖ = (c * ‖z - z'‖) / 2 := by ring
      rw [h4, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc c * ‖z - z'‖ ≤ _ := h1
        _ ≤ _ := h3
        _ = _ := by ring)
    (fun z => by
      obtain ⟨h1, h2, -⟩ := hclose z
      rw [Prod.norm_def]
      exact max_le (by simpa using h1) (by simpa using h2))
    (fun z => by
      obtain ⟨-, -, h3⟩ := hclose z
      rw [(hprod f hfd hf0 z).fderiv, (hprod u hus hu0 z).fderiv]
      refine le_trans ?_ h3
      have hS : 0 ≤ 1 + ‖z‖ := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hS
      set X := fderiv ℝ (fun w => aCoord H (f w)) z
      set Y := fderiv ℝ (fun w => proj H (f w)) z
      set X' := fderiv ℝ (fun w => aCoord H (u w)) z
      set Y' := fderiv ℝ (fun w => proj H (u w)) z
      have e : X.prod Y - X'.prod Y' = (X - X').prod (Y - Y') := by
        ext v <;> simp
      rw [e, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _)))
  refine ⟨fun z z' h => hinj (by simp only [h]), fun z => ?_⟩
  exact (injective_fderiv_aCoord_proj_comp_iff H hH f z (hfd z) (hf0 z)).1 (hdinj z)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ 1 f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      IsEmbeddedPlane f :=
  isEmbeddedPlane_of_isCylCloseTo_aux H hH J hJ P u hu huP hue
