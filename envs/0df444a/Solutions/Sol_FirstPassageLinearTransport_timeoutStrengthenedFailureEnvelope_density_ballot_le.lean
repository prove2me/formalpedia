-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_density_ballot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:58.969481+00:00
-- url     : https://prove2.me/submissions/9f44f57e-a555-4949-a9e8-df8fa3335b9f

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Theorems.Thm_FirstPassageLinearTransport_timeoutSeparatedFailureEnvelope_density_ballot_le
import Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedFailureEnvelope_card_le
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellMultiplicativeHit_quarter_le


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {M L S : ℕ} {H dHi D b₀ b R : ℝ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 1 ≤ L)
    (hH0 : 0 ≤ H)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (timeoutHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        D / (((p - 1 : ℕ) : ℝ) *
          Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hD : 0 ≤ D) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    (hR : 0 < R) :
    ((timeoutStrengthenedFailureEnvelope P K₀ M L S R).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (rStar : ℝ)) *
          (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
            ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) +
        4 / R := by
  have htimeout := timeoutSeparatedFailureEnvelope_density_ballot_le
    hrStar hStarHi hStarLo hM hLS hSM hL hH0 hnextPos hnextLt
    hsmall hTimes hInitial hHigh hLow hD hb₀ hb₀b
  have hheight := normalized_card_shellMultiplicativeHit_quarter_le hR M
  have hcardNat := timeoutStrengthenedFailureEnvelope_card_le
    P K₀ M L S R
  have hcard :
      ((timeoutStrengthenedFailureEnvelope P K₀ M L S R).card : ℝ) ≤
        ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) +
          ((shellMultiplicativeHit M (R / 4)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hdiv := div_le_div_of_nonneg_right hcard hpowM.le
  rw [add_div] at hdiv
  exact hdiv.trans (add_le_add htimeout hheight)
end FirstPassageLinearTransport
