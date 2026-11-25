-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.norm_conjugation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:04:37.416411+00:00
-- url     : https://prove2.me/submissions/5ff1deb9-9877-41ed-ae90-7464dc47c602

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : NormConjInvariant := by
  unfold NormConjInvariant
  intro s q r hq hr X _ Φ hΦ
  have hsr : ‖s r‖ = ‖r‖ := by
    have h1 : (s r) ^ 2 = (q : ℂ) := by rw [← map_pow, hr, map_natCast]
    have h2 : ‖s r‖ ^ 2 = ‖r‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h1, hr]
    rw [← Real.sqrt_sq (norm_nonneg (s r)), h2, Real.sqrt_sq (norm_nonneg r)]
  have hroot : ∀ (z : ℂ) (n : ℕ), 0 < n → z ^ n = 1 → ‖z‖ = 1 := fun z n hn hz => by
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  rcases hΦ x with h0 | ⟨ζ, n, k, hn, hζ, hx⟩
  · rw [h0, map_zero]
  · rw [hx, map_mul, map_zpow₀, norm_mul, norm_mul, norm_zpow, norm_zpow, hsr,
      hroot ζ n hn hζ, hroot (s ζ) n hn (by rw [← map_pow, hζ, map_one])]
end Formalism.HermitianLattices.IntegralLatticeDensity
