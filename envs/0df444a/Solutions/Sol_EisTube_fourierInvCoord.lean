-- Prove2me | solution 1 for EisTube.fourierInvCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:20.740997+00:00
-- url     : https://prove2.me/submissions/bbd787fd-9ccf-4d3c-8b13-c0cdb2e71d5e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomainStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftParametrisedIntegralStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Theorems.Thm_GlobalTheory_T_fourier_inversion_finite_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open EisTube
namespace EisTube
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y :=
  GlobalTheory.T.fourier_inversion_finite_dim
end EisTube
