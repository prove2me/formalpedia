-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_le_of_mem_antidiagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:07.044546+00:00
-- url     : https://prove2.me/submissions/70bef79c-14a6-4001-8a9c-1d5a21f1e6ad

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {A : Type*} [CommRing A] {σ : Type*}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add]
  omega
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
