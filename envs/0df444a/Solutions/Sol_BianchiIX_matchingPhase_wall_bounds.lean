-- Prove2me | solution 1 for BianchiIX.matchingPhase_wall_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:46:56.60633+00:00
-- url     : https://prove2.me/submissions/682db973-f88c-4c68-9af6-e91f0eddbccf

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWallDifferential
import Theorems.Thm_BianchiIX_matchingPhase_auxiliary_m_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_slope_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / 4 ≤ matchingPhaseSlope m v w ∧ matchingPhaseSlope m v w ≤ 1 := by
  have hp := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m + 1) hv
  have hn := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1) hw
  dsimp [matchingPhaseSlope]
  constructor <;> linarith only [hp.1, hp.2, hn.1, hn.2]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.matchingPhase_inverse_weighted_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |1 / matchingPhaseSlope m v w| ≤ 4 / 3 ∧
      |matchingPhaseVVariation m v w| ≤ 3 * v ^ 2 / μ ∧
      |matchingPhaseWVariation m v w| ≤ 3 * w ^ 2 / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hf := (matchingPhase_slope_bounds hμ hm hv hw).1
  have hf0 : 0 < matchingPhaseSlope m v w := by linarith only [hf]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have bound (K r : ℝ) (hK : μ / 2 ≤ K) : |(-r ^ 2) / (K * matchingPhaseSlope m v w)| ≤ 3 * r ^ 2 / μ := by
    have hK0 : 0 < K := by linarith only [hK, hμ0]
    have hprod : μ / 3 ≤ K * matchingPhaseSlope m v w := by
      have H := mul_le_mul hK hf (by norm_num : (0 : ℝ) ≤ 3 / 4) hK0.le
      nlinarith only [H, hμ0]
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg r), abs_of_pos (mul_pos hK0 hf0)]
    exact (div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hprod).trans_eq (by ring)
  refine ⟨?_, bound _ v (by linarith only [hp, hμ, (abs_le.mp hm).1]),
    bound _ w (by linarith only [hn, hμ, (abs_le.mp hm).1])⟩
  rw [abs_of_pos (by positivity : 0 < 1 / matchingPhaseSlope m v w)]
  exact (div_le_iff₀ hf0).mpr (by linarith only [hf])

end
end

private theorem BianchiIX.phaseNorm_weighted_ratio_bound {a r l : ℝ} (hl : 0 < l) (ha : l ≤ a) :
    |a * r ^ 2 / phaseNorm a r ^ 3| ≤ r ^ 2 / l ^ 2 := by
  have ha0 := hl.trans_le ha
  have hK := phaseNorm_pos (b := r) ha0
  have hKa := phaseNorm_ge (b := r) ha0.le
  rw [abs_of_nonneg (by positivity : 0 ≤ a * r ^ 2 / phaseNorm a r ^ 3)]
  calc
    _ ≤ phaseNorm a r * r ^ 2 / phaseNorm a r ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (sq_nonneg r)) (by positivity)
    _ = r ^ 2 / phaseNorm a r ^ 2 := by field_simp
    _ ≤ r ^ 2 / l ^ 2 := div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
      (pow_le_pow_left₀ hl.le (ha.trans hKa) 2)

theorem solution {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseSlopePartials m v w 2| ≤ 5 * v ^ 2 / μ ^ 2 ∧
    |matchingPhaseSlopePartials m v w 3| ≤ 5 * w ^ 2 / μ ^ 2 ∧
    |matchingPhaseWeightPartials m v w 2| ≤ 5 * v ^ 2 / μ ^ 2 ∧
    |matchingPhaseWeightPartials m v w 3| ≤ 5 * w ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have haux := matchingPhase_auxiliary_m_bounds (v := v) (w := w) hμ hm
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hfm : |matchingPhaseSlopeDm m v w| ≤ 9 / μ ^ 3 := by
    rw [abs_of_nonneg haux.1]
    apply haux.2.1.trans
    convert! div_le_div_of_nonneg_right (show 9 * (v ^ 2 + w ^ 2) ≤ 18 by linarith only [hv2, hw2])
      (by positivity : 0 ≤ 2 * μ ^ 3) using 1
    ring
  have hcorr : |matchingPhaseWeightDm m v w - matchingPhaseSlope m v w| ≤ 9 / μ ^ 3 := by
    have hp := phaseNorm_pos (b := v) (show 0 < m + 1 by linarith only [hμ, (abs_le.mp hm).1])
    have hn := phaseNorm_pos (b := w) (show 0 < m - 1 by linarith only [hμ, (abs_le.mp hm).1])
    have hq : 0 ≤ v ^ 2 / phaseNorm (m + 1) v ^ 3 := by positivity
    have hr : 0 ≤ w ^ 2 / phaseNorm (m - 1) w ^ 3 := by positivity
    have H := abs_sub (w ^ 2 / phaseNorm (m - 1) w ^ 3) (v ^ 2 / phaseNorm (m + 1) v ^ 3)
    rw [abs_of_nonneg hq, abs_of_nonneg hr] at H
    calc
      _ = |w ^ 2 / phaseNorm (m - 1) w ^ 3 - v ^ 2 / phaseNorm (m + 1) v ^ 3| := by
        dsimp [matchingPhaseWeightDm]
        congr 1
        ring
      _ ≤ matchingPhaseSlopeDm m v w := H.trans_eq (by dsimp [matchingPhaseSlopeDm]; ring)
      _ ≤ 9 / μ ^ 3 := by simpa only [abs_of_nonneg haux.1] using hfm
  have explicit_bound (a r : ℝ) (ha : 5 * μ / 8 ≤ a) :
      |a * r ^ 2 / phaseNorm a r ^ 3| ≤ 3 * r ^ 2 / μ ^ 2 := by
    apply (phaseNorm_weighted_ratio_bound (r := r) (by positivity : 0 < 5 * μ / 8) ha).trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (64 / 25 : ℝ) ≤ 3 by norm_num) (sq_nonneg r)) (sq_nonneg μ) using 1
    ring
  have hep := explicit_bound (m + 1) v (by linarith only [hμ, (abs_le.mp hm).1])
  have hen := explicit_bound (m - 1) w (by linarith only [hμ, (abs_le.mp hm).1])
  have hnep : |-(m + 1) * v ^ 2 / phaseNorm (m + 1) v ^ 3| ≤ 3 * v ^ 2 / μ ^ 2 := by
    simpa only [neg_mul, neg_div, abs_neg] using hep
  have hnen : |-(m - 1) * w ^ 2 / phaseNorm (m - 1) w ^ 3| ≤ 3 * w ^ 2 / μ ^ 2 := by
    simpa only [neg_mul, neg_div, abs_neg] using hen
  have mixed (r e δ q : ℝ) (he : |e| ≤ 3 * r ^ 2 / μ ^ 2)
      (hδ : |δ| ≤ 3 * r ^ 2 / μ) (hq : |q| ≤ 9 / μ ^ 3) : |e + δ * q| ≤ 5 * r ^ 2 / μ ^ 2 := by
    have Hprod : |δ * q| ≤ 27 * r ^ 2 / μ ^ 4 := by
      rw [abs_mul]
      exact (mul_le_mul hδ hq (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have Hprod' : |δ * q| ≤ 2 * r ^ 2 / μ ^ 2 := Hprod.trans (by
      calc
        _ ≤ 2 * μ ^ 2 * r ^ 2 / μ ^ 4 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hμ2]) (sq_nonneg r)) (by positivity)
        _ = _ := by field_simp)
    exact ((abs_add_le _ _).trans (add_le_add he Hprod')).trans_eq (by ring)
  exact ⟨mixed v _ _ _ hnep hvar.2.1 hfm, mixed w _ _ _ hnen hvar.2.2 hfm,
    mixed v _ _ _ hep hvar.2.1 hcorr, mixed w _ _ _ hnen hvar.2.2 hcorr⟩
