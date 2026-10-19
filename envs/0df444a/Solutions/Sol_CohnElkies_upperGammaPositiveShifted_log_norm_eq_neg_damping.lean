-- Prove2me | solution 1 for CohnElkies.upperGammaPositiveShifted_log_norm_eq_neg_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/6be7ae44-7dd0-4844-8f3e-ca6cf110dba1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_integral_upperGammaTruncatedDampingIntegrand
import Theorems.Thm_CohnElkies_integral_upperGammaTruncatedDampingIntegrand
import Theorems.Thm_CohnElkies_upperGammaLaplaceRate_log_ratio
import Theorems.Thm_CohnElkies_upperGammaEuler_log_norm_ratio
import Theorems.Thm_CohnElkies_tendsto_upperGammaEuler_log_norm_ratio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Real.log
        (‖Complex.Gamma
            (((ℓ * η / 2 : ℝ) : ℂ) +
              Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ /
          Real.Gamma (ℓ * η / 2)) =
      -upperGammaDamping ℓ η T := by
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hfinite :
      (fun n : ℕ =>
        Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖)) =ᶠ[atTop]
      (fun n : ℕ =>
        -(∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    calc
      Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖) =
          -(∑ k ∈ Finset.range (n + 1),
            Real.log
              (‖(m : ℂ) + Complex.I * (b : ℂ) +
                    (k : ℂ)‖ /
                (m + (k : ℝ)))) :=
        upperGammaEuler_log_norm_ratio hm b hn
      _ = -(∑ k ∈ Finset.range (n + 1),
            Real.log
              (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                  Complex.I * (T : ℂ)‖ /
                (η + 2 * (k : ℝ) / ℓ))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        simpa [m, b] using!
          (upperGammaLaplaceRate_log_ratio hℓ hη T k).symm
      _ = -(∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a) := by
        rw [integral_upperGammaTruncatedDampingIntegrand
          hℓ hη T n]
  have hlog := tendsto_upperGammaEuler_log_norm_ratio hm b
  have hdamping :=
    tendsto_integral_upperGammaTruncatedDampingIntegrand
      hℓ hη T
  have hmatch :=
    Filter.Tendsto.congr' hfinite.symm hdamping.neg
  have hidentity := tendsto_nhds_unique hlog hmatch
  have hdennorm :
      ‖Complex.Gamma (m : ℂ)‖ = Real.Gamma m := by
    rw [Complex.Gamma_ofReal]
    exact Complex.norm_of_nonneg
      (Real.Gamma_pos_of_pos hm).le
  rw [hdennorm] at hidentity
  change Real.log
    (‖Complex.Gamma
        ((m : ℂ) + Complex.I * (b : ℂ))‖ /
      Real.Gamma m) = -upperGammaDamping ℓ η T
  exact hidentity
end CohnElkies
