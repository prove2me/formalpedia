-- Prove2me | solution 1 for BianchiIX.connectionWeakClockPartials_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:34:38.029773+00:00
-- url     : https://prove2.me/submissions/d69b9c0e-ccbc-46e3-abca-b19f37dce935

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
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

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_strong_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000) :
    connectionStrongRate m u v w ≤ -μ ^ 2 / 4 := by
  have hm0 : 7 * μ / 8 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0)
    (show 0 ≤ m + 7 * μ / 8 by linarith only [hm0, hμ])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionStrongRate
  nlinarith only [hm2, hu2, hμ, sq_nonneg (μ - 4), sq_nonneg (v - w)]

end
end

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

private theorem BianchiIX.connection_amplitude_base_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |1 + coupling u v w| ≤ 2 ∧ |connectionStrongClockRate m u v w| ≤ 2 * μ ∧
      |m + connectionStrongClockRate m u v w| ≤ 4 * μ ∧ |v + w - 2 * u| ≤ 3 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hm1 : m ≤ 9 * μ / 8 := by linarith only [hμ, (abs_le.mp hm).2]
  have hm2 := pow_le_pow_left₀ hm0 hm1 2
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hd2 : (v - w) ^ 2 ≤ 1 := by nlinarith only [sq_abs (v - w), pow_le_pow_left₀ (abs_nonneg _) hd 2]
  have hN : |connectionStrongRate m u v w| ≤ μ ^ 2 := by
    have H := connection_strong_rate_le (v := v) (w := w) hμ hm hu
    rw [abs_le]
    dsimp [connectionStrongRate] at *
    constructor <;> nlinarith only [hm2, hd2, sq_nonneg u, sq_nonneg μ, H]
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have ha : |connectionStrongClockRate m u v w| ≤ 2 * μ := by
    rw [connectionStrongClockRate, abs_div, abs_of_pos hD0]
    apply (div_le_iff₀ hD0).mpr
    have H := mul_le_mul_of_nonneg_left hD hμ0.le
    nlinarith only [hN, H]
  refine ⟨?_, ha, ?_, ?_⟩
  · have hC := connection_coupling_bounds hu.1 hv hw
    apply abs_le.mpr
    constructor <;> nlinarith only [hC.1, hC.2, hu.2, hu2]
  · exact (abs_add_le _ _).trans ((add_le_add (by simpa [abs_of_nonneg hm0] using hm1) ha).trans
      (by linarith only [hμ0]))
  · apply abs_le.mpr
    constructor <;> linarith only [hu.1, hu.2, hv.1, hv.2, hw.1, hw.2]

theorem solution {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionWeakClockPartials m u v w 0| ≤ 64 / μ ^ 2 ∧
    |connectionWeakClockPartials m u v w 1| ≤ 64 * u / μ ∧
    |connectionWeakClockPartials m u v w 2| ≤ 64 * (v ^ 2 / μ ^ 3 + u * v / μ) ∧
    |connectionWeakClockPartials m u v w 3| ≤ 64 * (w ^ 2 / μ ^ 3 + u * w / μ) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hm1 : |m| ≤ 2 * μ := by rw [abs_of_nonneg hm0]; linarith only [hμ, (abs_le.mp hm).2]
  obtain ⟨hC, _, _, hS⟩ := connection_amplitude_base_bounds hμ hm hu hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have hD2pos : 0 < connectionSpeed m u v w ^ 2 := by positivity
  have hf := (matchingPhase_slope_bounds hμ hm hv hw).1
  have hf0 : 0 < matchingPhaseSlope m v w := by linarith only [hf]
  have hvariation := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have wall_bound (r e : ℝ) (hr : 0 ≤ r) (he : |e| ≤ 3 * r ^ 2 / μ) :
      |(2 * (1 + coupling u v w) * e - 2 * m * u * r) / connectionSpeed m u v w ^ 2| ≤
        64 * (r ^ 2 / μ ^ 3 + u * r / μ) := by
    have H1 : |2 * (1 + coupling u v w) * e| ≤ 12 * r ^ 2 / μ := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num)) he (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have H2 : |2 * m * u * r| ≤ 4 * μ * u * r := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hu.1, abs_of_nonneg hr]
      have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm1 (by norm_num : (0 : ℝ) ≤ 2)) hu.1) hr
      nlinarith only [H]
    have H := (abs_sub _ _).trans (add_le_add H1 H2)
    rw [abs_div, abs_of_pos hD2pos]
    calc
      _ ≤ (12 * r ^ 2 / μ + 4 * μ * u * r) / (μ ^ 2 / 4) :=
        div_le_div₀ (by positivity) H (by positivity) hD2
      _ = 48 * (r ^ 2 / μ ^ 3) + 16 * (u * r / μ) := by field_simp; ring
      _ ≤ 64 * (r ^ 2 / μ ^ 3 + u * r / μ) := by
        have H3 : 0 ≤ r ^ 2 / μ ^ 3 := by positivity
        have H4 : 0 ≤ u * r / μ := by positivity
        linarith only [H3, H4]
  refine ⟨?_, ?_, wall_bound v _ hv.1 hvariation.2.1, wall_bound w _ hw.1 hvariation.2.2⟩
  · have H : μ ^ 2 / 8 ≤ connectionSpeed m u v w ^ 2 * matchingPhaseSlope m v w := by
      have H' := mul_le_mul hD2 hf (by norm_num : (0 : ℝ) ≤ 3 / 4) hD2pos.le
      nlinarith only [H', sq_nonneg μ]
    change |2 * (1 + coupling u v w) / (connectionSpeed m u v w ^ 2 * matchingPhaseSlope m v w)| ≤ _
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (mul_pos hD2pos hf0)]
    calc
      _ ≤ 4 / (μ ^ 2 / 8) := div_le_div₀ (by positivity) (by linarith only [hC]) (by positivity) H
      _ = 32 / μ ^ 2 := by ring
      _ ≤ 64 / μ ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg μ)
  · change |-(2 * m * u * (v + w - 2 * u)) / connectionSpeed m u v w ^ 2| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg hu.1, abs_of_pos hD2pos]
    have H := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 (by norm_num)) hu.1)
      hS (abs_nonneg _) (by positivity : 0 ≤ 2 * (2 * μ) * u)
    calc
      _ ≤ (2 * (2 * μ) * u * 3) / (μ ^ 2 / 4) := div_le_div₀ (by positivity) H (by positivity) hD2
      _ = 48 * u / μ := by field_simp; ring
      _ ≤ 64 * u / μ := div_le_div_of_nonneg_right (by nlinarith only [hu.1]) hμ0.le
