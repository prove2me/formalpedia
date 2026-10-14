-- Prove2me | solution 1 for DbarRegularity.convolution_lp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:08:03.500904+00:00
-- url     : https://prove2.me/submissions/ca889d97-8187-4569-bb24-cc4e3023d09f

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Fourier.LpSpace
import Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le_of_hormander
import Theorems.Thm_DbarRegularity_convolution_l2_bound
import Theorems.Thm_DbarRegularity_hormander_of_norm_fderiv_le
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

theorem convolution_lp_bound_aux (d : ℕ) (p : ℝ) (hp : 1 < p) (B : ℝ) :
    ∃ A : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume),
      (∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B) →
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f 1 volume → MemLp f (ENNReal.ofReal p) volume →
        MemLp (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ∧
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: a one-point probability space, where all `L^p` norms agree
    refine ⟨B.toNNReal, fun K hK hFT _ _ f _ hf => ?_⟩
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ = 1 := by
      rw [volume_euclideanSpace_eq_dirac]; simp
    haveI : IsProbabilityMeasure (volume : Measure (EuclideanSpace ℝ (Fin 0))) := ⟨hvol⟩
    have hconst : ∀ (u : EuclideanSpace ℝ (Fin 0) → ℂ) (r : ℝ≥0∞), r ≠ 0 →
        eLpNorm u r volume = ‖u 0‖ₑ := by
      intro u r hr
      have hu : u = fun _ => u 0 := funext fun x => congrArg u (Subsingleton.elim x 0)
      rw [hu, eLpNorm_const _ hr (IsProbabilityMeasure.ne_zero _), hvol, ENNReal.one_rpow,
        mul_one]
    have hf2 : MemLp f 2 volume := ⟨hf.1, by rw [hconst f 2 two_ne_zero]; exact enorm_lt_top⟩
    obtain ⟨h1, h2⟩ := convolution_l2_bound K hK B hFT f hf2
    rw [hconst _ _ two_ne_zero, hconst f _ two_ne_zero] at h2
    refine ⟨⟨h1.1, by rw [hconst _ _ hp0]; exact enorm_lt_top⟩, ?_⟩
    rw [hconst _ _ hp0, hconst f _ hp0]
    exact h2
  · -- `d > 0`
    obtain ⟨Ch, hCh⟩ := hormander_of_norm_fderiv_le d
    obtain ⟨A, hA⟩ := eLpNorm_integral_mul_sub_le_of_hormander hd p hp (Ch * B).toNNReal
      B.toNNReal
    refine ⟨A, fun K hK hFT hC hD f hf1 hf => ?_⟩
    have hbound := hA K hK (fun y hy => hCh B K hC hD y hy)
      (fun g hg => (convolution_l2_bound K hK B hFT g hg).2) f
      (memLp_one_iff_integrable.1 hf1) hf
    exact ⟨⟨aestronglyMeasurable_integral_mul_sub K f hK.1 hf.1,
      hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩, hbound⟩

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (d : ℕ) (p : ℝ) (hp : 1 < p) (B : ℝ) :
    ∃ A : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume),
      (∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B) →
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f 1 volume → MemLp f (ENNReal.ofReal p) volume →
        MemLp (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ∧
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
  convolution_lp_bound_aux d p hp B
