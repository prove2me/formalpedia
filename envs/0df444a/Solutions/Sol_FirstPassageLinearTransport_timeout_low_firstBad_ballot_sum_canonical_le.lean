-- Prove2me | solution 1 for FirstPassageLinearTransport.timeout_low_firstBad_ballot_sum_canonical_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:19.604597+00:00
-- url     : https://prove2.me/submissions/001c5744-9b5d-4fc0-9aa8-080ca3a94050

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_density_le
import Theorems.Thm_FirstPassageLinearTransport_reciprocal_sqrt_entropy_tail_exact_rate_Icc_le

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 1 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H D b₀ b : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        D / (((p - 1 : ℕ) : ℝ) *
          Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hD : 0 ≤ D) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ∑ p ∈ Finset.Icc (L + 1) S,
        ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) *
        (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
          ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) := by
  have hterm : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * D *
          (((p + 1 : ℕ) : ℝ) /
            (((p - 1 : ℕ) : ℝ) *
              Real.sqrt ((p - 1 : ℕ) : ℝ)) *
                Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
    intro p hpI
    have hpI' := Finset.mem_Icc.mp hpI
    have hp1 : 1 ≤ p := by omega
    have hpM : p < M := hpI'.2.trans_lt hSM
    have hbase := timeoutFirstBadSourcesAtRank_density_le
      (S := S) hrStar hStarHi hStarLo hM hp1
      (hnextPos p hpI) (hnextLt p hpI) hpM (hsmall p hpI)
      (hTimes p hpI) (hTarget p hpI)
    calc
      _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) *
          (D / (((p - 1 : ℕ) : ℝ) *
            Real.sqrt ((p - 1 : ℕ) : ℝ)) *
              Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := hbase
      _ = _ := by ring
  have htail := reciprocal_sqrt_entropy_tail_exact_rate_Icc_le
    hb₀ hb₀b hL hLS
  have hH0 : 0 ≤ H := by
    have hcard0 : 0 ≤
        ((timeoutFeasibleTimes P K₀ L M S (L + 1)).card : ℝ) := by positivity
    exact hcard0.trans
      (hTimes (L + 1) (Finset.mem_Icc.mpr ⟨le_rfl, hLS⟩))
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) * D := by positivity
  calc
    _ ≤ ∑ p ∈ Finset.Icc (L + 1) S,
        H * (1 + 6 / (rStar : ℝ)) * D *
          (((p + 1 : ℕ) : ℝ) /
            (((p - 1 : ℕ) : ℝ) *
              Real.sqrt ((p - 1 : ℕ) : ℝ)) *
                Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) :=
      Finset.sum_le_sum hterm
    _ = (H * (1 + 6 / (rStar : ℝ)) * D) *
        ∑ p ∈ Finset.Icc (L + 1) S,
          (((p + 1 : ℕ) : ℝ) /
            (((p - 1 : ℕ) : ℝ) *
              Real.sqrt ((p - 1 : ℕ) : ℝ)) *
                Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (H * (1 + 6 / (rStar : ℝ)) * D) *
        ((3 / Real.sqrt L) * Real.exp (-(b * (L : ℝ))) *
          weightedTailConstant b₀ (b₀ / 2)) :=
      mul_le_mul_of_nonneg_left htail hcoef0
    _ = H * (1 + 6 / (rStar : ℝ)) *
        (3 * D * weightedTailConstant b₀ (b₀ / 2)) *
          ((1 / Real.sqrt L) * Real.exp (-(b * (L : ℝ)))) := by ring
end FirstPassageLinearTransport
