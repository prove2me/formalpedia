-- Prove2me | solution 1 for DbarRegularity.dbar_lp_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:44:30.934412+00:00
-- url     : https://prove2.me/submissions/76328ef9-0e96-4e11-8133-d800565f920f

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_euclidean
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic



namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem dbar_lp_estimate_aux (n : ℕ) (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ∃ c : ℝ, 1 < c ∧ ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ ∞ φ → tsupport φ ⊆ ball 0 R →
      (eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume ^ p +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume ^ p +
          eLpNorm φ (ENNReal.ofReal p) volume ^ p) ^ (1 / p)
        ≤ ENNReal.ofReal c * eLpNorm (dbar φ) (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA⟩ := cauchyRiemann_lp_euclidean n p hp
  have hA0 : (0 : ℝ) ≤ A := A.coe_nonneg
  set c : ℝ := (1 + 2 * R) * (A + 1) + 1 with hc
  refine ⟨c, by nlinarith, fun φ hφ hsupp => ?_⟩
  have hp0 : 0 < p := by linarith
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hcs : HasCompactSupport φ :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport φ)
      (hsupp.trans ball_subset_closedBall)
  set a := eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume
  set b := eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume
  set d := eLpNorm φ (ENNReal.ofReal p) volume
  set D := eLpNorm (dbar φ) (ENNReal.ofReal p) volume
  have hab : a + b ≤ A * D := hA φ hφ1 hcs
  have hd : d ≤ ENNReal.ofReal (2 * R) * a :=
    eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball R p hp.le φ hφ1 hsupp
  have hq0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hq1 : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp.le
  have hroot : ∀ x : ℝ≥0∞, (x ^ p) ^ (1 / p) = x := fun x => by
    rw [one_div, ENNReal.rpow_rpow_inv hp0.ne']
  have hsum : (a ^ p + b ^ p + d ^ p) ^ (1 / p) ≤ a + b + d := by
    calc (a ^ p + b ^ p + d ^ p) ^ (1 / p)
        ≤ (a ^ p + b ^ p) ^ (1 / p) + (d ^ p) ^ (1 / p) :=
          ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1
      _ ≤ (a ^ p) ^ (1 / p) + (b ^ p) ^ (1 / p) + (d ^ p) ^ (1 / p) := by
          gcongr; exact ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1
      _ = a + b + d := by rw [hroot, hroot, hroot]
  have key : (1 + ENNReal.ofReal (2 * R)) * (A : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [show (1 : ℝ≥0∞) + ENNReal.ofReal (2 * R) = ENNReal.ofReal (1 + 2 * R) by
      rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_one]]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  calc (a ^ p + b ^ p + d ^ p) ^ (1 / p) ≤ a + b + d := hsum
    _ ≤ (a + b) + ENNReal.ofReal (2 * R) * (a + b) := by
        gcongr
        exact hd.trans (by gcongr; exact le_self_add)
    _ = (1 + ENNReal.ofReal (2 * R)) * (a + b) := by ring
    _ ≤ (1 + ENNReal.ofReal (2 * R)) * (A * D) := by gcongr
    _ = ((1 + ENNReal.ofReal (2 * R)) * A) * D := by ring
    _ ≤ ENNReal.ofReal c * D := by gcongr

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (n : ℕ) (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ∃ c : ℝ, 1 < c ∧ ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ ∞ φ → tsupport φ ⊆ ball 0 R →
      (eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume ^ p +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume ^ p +
          eLpNorm φ (ENNReal.ofReal p) volume ^ p) ^ (1 / p)
        ≤ ENNReal.ofReal c * eLpNorm (dbar φ) (ENNReal.ofReal p) volume :=
  dbar_lp_estimate_aux n p R hp hR
