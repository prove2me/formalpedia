-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_snd_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:27.322444+00:00
-- url     : https://prove2.me/submissions/3851f6d9-bfc4-4fb3-812e-e92e8ddfff24

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
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h1 : x.1 ≠ 0) : x.2.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.1.degree ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
  rw [← hx, map_add]
  omega
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
