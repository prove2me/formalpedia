-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellTargetHeightFailure_ge_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:34.20394+00:00
-- url     : https://prove2.me/submissions/9ad00185-292e-4b68-95b0-c7b47883f9e2

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_shellPrefixMultiplicativeHit_subset_shellTargetHeightFailure
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellPrefixMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_reciprocal_finite_multiplicative_maximum


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {u : ℝ} (hu : 1 ≤ u)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellTargetHeightFailure M f u).card : ℝ) / (2 : ℝ) ^ M := by
  have hfinite := reciprocal_finite_multiplicative_maximum hu hh hlog
  rw [← normalized_card_shellPrefixMultiplicativeHit M h hhM u] at hfinite
  have hcardNat := Finset.card_le_card
    (shellPrefixMultiplicativeHit_subset_shellTargetHeightFailure
      (u := u) hhM htarget)
  have hcard :
      ((shellPrefixMultiplicativeHit M h hhM u).card : ℝ) ≤
        (shellTargetHeightFailure M f u).card := by
    exact_mod_cast hcardNat
  exact hfinite.1.trans <|
    div_le_div_of_nonneg_right hcard (by positivity)
end FirstPassageLinearTransport
