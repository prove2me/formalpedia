-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.total_named_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:35.630799+00:00
-- url     : https://prove2.me/submissions/02f37396-3ec1-4295-9bca-af30d2052c0c

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution (d D T c G PH Pη Pd PD PQ DivisibilityWeightConstant RR γ L κ fr lδ ρ ρ' : ℝ)
    (hd : 0 ≤ d) (hD : 1 ≤ D) (hT : 1 ≤ T) (hG : 0 ≤ G) (hPH : 0 ≤ PH) (hPD : 0 ≤ PD) (hPQ : 0 ≤ PQ)
    (hκ : 0 ≤ κ) (hS2 : T * L ≤ 2 * κ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ)) :
    d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)
        + ρ * PD * κ + ρ' * PQ * κ ≤
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) := by
  have hT0 : 0 < T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hLT : L ≤ 2 * κ / T := by
    rw [le_div_iff₀ hT0]
    linarith
  have hDD : (D + 4) * (D + 1) ≤ 10 * D ^ 2 := by nlinarith
  have hk : 0 ≤ 2 * κ / T := by positivity
  have hGP : 0 ≤ 3 * G + 9 * PH := by positivity
  have e1 : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L ≤ (60 * G + 180 * PH) * D ^ 2 * κ / T := by
    calc (D + 4) * (D + 1) * (3 * G + 9 * PH) * L
        ≤ (D + 4) * (D + 1) * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_left hLT (by positivity)
      _ ≤ 10 * D ^ 2 * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hGP) hk
      _ = (60 * G + 180 * PH) * D ^ 2 * κ / T := by ring
  have hPd0 : 0 ≤ Pd := le_trans hlδ0 hlδ
  have e2 : lδ ≤ Pd * T := hlδ.trans (le_mul_of_one_le_right hPd0 hT)
  have hX : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη ≤ ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) := by
    have ea : (5 * G * fr + Pd) * T = 5 * G * fr * T + Pd * T := by ring
    have eb : Pη / 2 * T * c = 1 / 2 * T * c * Pη := by ring
    linarith
  have g1 := mul_le_mul_of_nonneg_left hX hd
  have f1 : ρ * (PD * κ) ≤ (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg hPD hκ)
  have f2 : ρ' * ((PD + PQ) * κ) ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) :=
    mul_le_mul_of_nonneg_right hρ' (mul_nonneg (add_nonneg hPD hPQ) hκ)
  have e5 : 22 * D ^ 2 * d / T * (PD * κ) ≤ d * (40 * PD * D ^ 2 * κ / T) := by
    have h0 : 0 ≤ d * PD * D ^ 2 * κ / T := by positivity
    have ea : 22 * D ^ 2 * d / T * (PD * κ) = 22 * (d * PD * D ^ 2 * κ / T) := by ring
    have eb : d * (40 * PD * D ^ 2 * κ / T) = 40 * (d * PD * D ^ 2 * κ / T) := by ring
    rw [ea, eb]
    linarith
  have eq1 : d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) =
      d * ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) + d * (40 * PD * D ^ 2 * κ / T) +
        d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) := by ring
  have eq2 : ρ * PD * κ + ρ' * PQ * κ = ρ * (PD * κ) + ρ' * ((PD + PQ) * κ) - ρ' * (PD * κ) := by ring
  have eq3 : (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) = ρ' * (PD * κ) + 22 * D ^ 2 * d / T * (PD * κ) := by
    ring
  rw [eq1]
  linarith
end Formalism.MainNotions.Gaps.T0
