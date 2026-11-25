-- Prove2me | solution 1 for FiniteEnergyPlane.isFastPlane_exp_smul_comp_affine
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:30:10.93211+00:00
-- url     : https://prove2.me/submissions/fb103904-b57c-49f5-a933-c7a3025cb707

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_comp_exp_mul_mem_embeddedFastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_comp_add_smul
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_shiftA



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isFastPlane_exp_smul_comp_affine_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ)
    (c : ℝ) (A B : ℂ) (hA : A ≠ 0) :
    IsFastPlane H J (fun z => Real.exp (2 * c) • u (A * z + B)) ∧
      IsNondegenerateEnd H (fun z => Real.exp (2 * c) • u (A * z + B)) cylInf P 1 ∧
      IsEmbeddedPlane (fun z => Real.exp (2 * c) • u (A * z + B)) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, 2 * π * α = Complex.arg A :=
    ⟨Complex.arg A / (2 * π), by field_simp⟩
  have hE : Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hAE : (‖A‖ : ℂ) * Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) = A := by
    rw [hα]; exact Complex.norm_mul_exp_arg_mul_I A
  have hm := comp_exp_mul_mem_embeddedFastPlaneSet H hH J hJ P K γ u hu α
  generalize Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) = E at hE hAE hm
  obtain ⟨⟨h1, h2, -, -⟩, h3⟩ := hm
  obtain ⟨k1, k2, k3⟩ := isFastPlane_comp_add_smul H hH J hJ P _ h1 h2 h3 (B / E) ‖A‖
    (norm_pos_iff.2 hA)
  have he : (fun z : ℂ => u (E * (B / E + ‖A‖ • z))) = fun z => u (A * z + B) := by
    funext z
    congr 1
    rw [Complex.real_smul, mul_add, mul_div_cancel₀ _ hE]
    linear_combination z * hAE
  simp only [he] at k1 k2 k3
  refine ⟨isFastPlane_shiftA H hH J hJ _ k1 c,
    isNondegenerateEnd_shiftA H hH _ (fun z => k1.1.2.1 z trivial) _ P 1 k2 c, ?_, ?_⟩
  · intro z w h
    exact k3.1 (smul_right_injective _ (Real.exp_ne_zero (2 * c)) h)
  · intro z v w h
    have hd : DifferentiableAt ℝ (fun z => u (A * z + B)) z :=
      (contDiffOn_univ.1 k1.1.1).differentiable (by simp) z
    have hf : fderiv ℝ (fun z => Real.exp (2 * c) • u (A * z + B)) z =
        Real.exp (2 * c) • fderiv ℝ (fun z => u (A * z + B)) z :=
      (hd.hasFDerivAt.const_smul (Real.exp (2 * c))).fderiv
    rw [hf] at h
    exact k3.2 z (smul_right_injective _ (Real.exp_ne_zero (2 * c)) h)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ)
    (c : ℝ) (A B : ℂ) (hA : A ≠ 0) :
    IsFastPlane H J (fun z => Real.exp (2 * c) • u (A * z + B)) ∧
      IsNondegenerateEnd H (fun z => Real.exp (2 * c) • u (A * z + B)) cylInf P 1 ∧
      IsEmbeddedPlane (fun z => Real.exp (2 * c) • u (A * z + B)) :=
  isFastPlane_exp_smul_comp_affine_aux H hH J hJ P K γ u hu c A B hA
