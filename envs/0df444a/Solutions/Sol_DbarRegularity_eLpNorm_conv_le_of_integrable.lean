-- Prove2me | solution 1 for DbarRegularity.eLpNorm_conv_le_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:28:47.305985+00:00
-- url     : https://prove2.me/submissions/ef45619f-b7f2-4f68-8523-f6d8198f4433

import Mathlib.Analysis.Fourier.LpSpace
import Theorems.Thm_DbarRegularity_eLpNorm_conv_le_aux
import Mathlib.MeasureTheory.Function.ContinuousMapDense



namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- The `L²` bound for `f ∈ L¹ ∩ L²`. -/
theorem eLpNorm_conv_le_of_integrable {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume)
    (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hc : eLpNorm f 1 volume ≠ ⊤ := (memLp_one_iff_integrable.2 hf1).2.ne
  obtain ⟨ε, hε, hεc⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 2 * eLpNorm f 1 volume)
    (b := (δ : ℝ≥0∞)) (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hc) (by exact_mod_cast hδ.ne')
  obtain ⟨K', hK's, hKK', hK'c, hK'2⟩ :=
    hK.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top (ε := (ε : ℝ≥0∞))
      (by exact_mod_cast hε.ne')
  calc eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume
      ≤ ENNReal.ofReal B * eLpNorm f 2 volume +
          2 * (eLpNorm (K - K') 2 volume * eLpNorm f 1 volume) :=
        eLpNorm_conv_le_aux K hK B hB f hf1 hf2 K' hK'c hK's hK'2
    _ ≤ ENNReal.ofReal B * eLpNorm f 2 volume + 2 * ((ε : ℝ≥0∞) * eLpNorm f 1 volume) := by
        gcongr
    _ ≤ ENNReal.ofReal B * eLpNorm f 2 volume + δ := by
        gcongr
        calc 2 * ((ε : ℝ≥0∞) * eLpNorm f 1 volume) = (ε : ℝ≥0∞) * (2 * eLpNorm f 1 volume) := by
              ring
          _ ≤ δ := hεc.le

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

theorem solution {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume)
    (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume :=
  eLpNorm_conv_le_of_integrable K hK B hB f hf1 hf2
