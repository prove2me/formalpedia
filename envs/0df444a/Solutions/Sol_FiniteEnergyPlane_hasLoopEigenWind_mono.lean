-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopEigenWind_mono
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:05:03.284218+00:00
-- url     : https://prove2.me/submissions/f1efca11-da2e-414a-a245-89599a26bdd8

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_nonneg_of_hasDerivAt_im
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_loopEigen



namespace FiniteEnergyPlane

open scoped ContDiff

theorem hasLoopEigenWind_mono_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k₁ k₂ : ℤ}
    (h₁ : HasLoopEigenWind Sinf μ₁ k₁) (h₂ : HasLoopEigenWind Sinf μ₂ k₂) (hμ : μ₁ < μ₂) :
    k₁ ≤ k₂ := by
  obtain ⟨⟨e₁, he₁⟩, hw₁⟩ := h₁
  obtain ⟨⟨e₂, he₂⟩, hw₂⟩ := h₂
  have hg := hasLoopWind_mul (hasLoopWind_conj (hw₁ e₁ he₁)) (hw₂ e₂ he₂)
  have := hasLoopWind_nonneg_of_hasDerivAt_im hg (sub_pos.2 hμ)
    (fun t => hasDerivAt_im_conj_mul_loopEigen Sinf hSinf he₁ he₂ t)
  omega

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k₁ k₂ : ℤ}
    (h₁ : HasLoopEigenWind Sinf μ₁ k₁) (h₂ : HasLoopEigenWind Sinf μ₂ k₂) (hμ : μ₁ < μ₂) :
    k₁ ≤ k₂ :=
  hasLoopEigenWind_mono_aux Sinf hSinf hSinf' h₁ h₂ hμ
