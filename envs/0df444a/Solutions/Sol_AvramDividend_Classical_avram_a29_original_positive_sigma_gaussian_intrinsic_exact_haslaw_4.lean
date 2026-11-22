-- Prove2me | solution 4 for AvramDividend.Classical.avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:32:22.707268+00:00
-- url     : https://prove2.me/submissions/1e905244-b655-4273-acb2-c153ff4ae3ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Original positive-sigma Gaussian law, partitioned by true negative
   jump intensity and t=0. A genuine OPEN same-source positive-time MGF
   lemma is used only in the positive-time nonzero-jump branch. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ t : ℝ≥0,
      HasLaw (G t)
        (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  let v : ℝ≥0 :=
    NNReal.mk ((t : ℝ) * X.σ ^ 2)
      (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
  have hMeas : AEMeasurable (G t) P :=
    avram_a31_original_gaussian_source_ae_representative_measurable_20261114
      X R hR G hEq t
  by_cases hNu : X.ν = 0
  · have hZeroLaw :=
      avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
        X hX hNu R hR t
    have hGt : (G t) =ᵐ[P] (R t) :=
      hEq.mono (fun ω hω => hω t)
    have hv :
        (NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t = v := by
      apply Subtype.ext
      change X.σ ^ 2 * (t : ℝ) = (t : ℝ) * X.σ ^ 2
      ring
    refine ⟨hMeas, ?_⟩
    calc
      P.map (G t) = P.map (R t) := Measure.map_congr hGt
      _ = gaussianReal 0 ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) :=
        hZeroLaw
      _ = gaussianReal 0 v := by rw [hv]
  · by_cases ht : t = 0
    · subst t
      have hChar :=
        avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
          X R hR G hEq
      have hZero :=
        avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
          (G 0) 0 hMeas hChar
      simpa [v] using hZero
    · have htpos : 0 < t := lt_of_le_of_ne (zero_le) (Ne.symm ht)
      have hMGF :=
        avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
          X hX hFinite hPositive hNu R hR G hEq t htpos
      apply avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
        P (G t) hMeas v
      · intro θ hθ
        exact (hMGF θ hθ).1
      · intro θ hθ
        exact (hMGF θ hθ).2

