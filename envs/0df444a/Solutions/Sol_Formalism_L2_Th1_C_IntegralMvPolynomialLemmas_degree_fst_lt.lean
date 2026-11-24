-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_fst_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:05.673445+00:00
-- url     : https://prove2.me/submissions/d2487daf-9c54-479f-81a8-1a81a7d01a13

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
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h2 : x.2 ≠ 0) : x.1.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)
  rw [← hx, map_add]
  omega
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
