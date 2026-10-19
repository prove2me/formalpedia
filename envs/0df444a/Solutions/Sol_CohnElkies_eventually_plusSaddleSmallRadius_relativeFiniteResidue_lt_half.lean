-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/92b84814-b17a-4977-8d49-94295ebf5501

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadius_relativeFiniteResidue_error
import Theorems.Thm_CohnElkies_eventually_saddleSmallResidueTruncation_double_le
import Theorems.Thm_CohnElkies_eventually_saddleSmallResidueTruncation_dominates_window
import Theorems.Thm_CohnElkies_saddleSmallResidue_tail_le_majorant
import Theorems.Thm_CohnElkies_saddleSmallResidue_coefficient_le_majorant
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueRelativeErrorMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by
  obtain ⟨K, hK, hfinite⟩ :=
    exists_plusSaddleSmallRadius_relativeFiniteResidue_error
      hε horder
  have hmajor :=
    (tendsto_saddleSmallResidueRelativeErrorMajorant K C).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards
    [hmajor,
      eventually_saddleSmallResidueTruncation_double_le,
      eventually_saddleSmallResidueTruncation_dominates_window hC,
      eventually_ge_atTop (1 : ℝ)]
    with ℓ hsmall hN hwindow hℓ
  intro y hy hyupper
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hratio := hwindow y hy hyupper
  have hbound := hfinite ℓ hℓpos
    (saddleSmallResidueTruncation ℓ) hN y hy hratio
  have hcoeff := saddleSmallResidue_coefficient_le_majorant
    hK hC hℓ hy hyupper
  have htail := saddleSmallResidue_tail_le_majorant
    hy hyupper
  have htailtwo :
      2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) ≤
        2 * saddleSmallResidueTailMajorant C ℓ := by
    calc
      2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) =
        2 * (Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ))) := by
        ring
      _ ≤ 2 * saddleSmallResidueTailMajorant C ℓ :=
        mul_le_mul_of_nonneg_left htail
          (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.exp y *
        |(∑ n ∈ Finset.range
            (saddleSmallResidueTruncation ℓ + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-y)| ≤
      (K / ℓ) *
          Real.exp
            (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
          (2 * y + y ^ 2) * Real.exp (2 * y) +
        2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) :=
      hbound
    _ ≤ saddleSmallResidueCoefficientMajorant K C ℓ +
          2 * saddleSmallResidueTailMajorant C ℓ := by
      exact add_le_add hcoeff htailtwo
    _ < 1 / 2 := by
      exact hsmall
end CohnElkies
