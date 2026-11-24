-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lemSSupBound_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:48.934701+00:00
-- url     : https://prove2.me/submissions/3381e25e-793a-4370-8598-66edc70ae51a

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_cut_scale
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_fourier_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hE : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula) : Formalism.HermitianLatticeCounting.ExpansionTerms.LemSSupBound := by
  intro φ x M hc hi hx hb c
  obtain ⟨hI, hV⟩ := hE 3 (x / π) (by norm_num) (div_pos hx pi_pos)
  have hbd : ∀ w : ℂ, ‖𝓕 φ w‖ ≤ M * TruncationCutoff 3 (x / π) ‖w‖ := by
    intro w
    rw [gl_fourier_eq, ← gl_cut_scale]
    have := hb (-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))
    have hn : ‖(-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))‖ = π * ‖w‖ := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, RCLike.norm_conj,
        Real.norm_of_nonneg pi_pos.le]
    rwa [hn] at this
  have hcont : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have hFi : Integrable (𝓕 φ) :=
    (hI.const_mul M).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hinv : 𝓕⁻ (𝓕 φ) c = φ c := hi.fourierInv_fourier_eq hFi hc.continuousAt
  rw [← hinv, Real.fourierInv_eq]
  calc ‖∫ v, 𝐞 ⟪v, c⟫ • 𝓕 φ v‖ ≤ ∫ v, ‖𝐞 ⟪v, c⟫ • 𝓕 φ v‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖𝓕 φ v‖ := by simp_rw [Circle.norm_smul]
    _ ≤ ∫ v : ℂ, M * TruncationCutoff 3 (x / π) ‖v‖ := integral_mono hFi.norm (hI.const_mul M) hbd
    _ = M * (π * (x / π) ^ 2 * (3 / (3 - 2))) := by rw [integral_const_mul, hV]
    _ = 3 / π * x ^ 2 * M := by
      field_simp
      ring
end Formalism.HermitianLatticeCounting.P
