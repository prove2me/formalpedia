-- Prove2me | solution 1 for BianchiIX.connectionPhaseGPartials_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:53:01.735465+00:00
-- url     : https://prove2.me/submissions/296fdf43-d0cb-4501-822f-a5d5e10fd40d

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseKernel
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeight
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseDirection
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWallDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseNumerator
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Theorems.Thm_BianchiIX_matchingPhase_auxiliary_m_bounds
import Theorems.Thm_BianchiIX_matchingPhase_wall_bounds
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

private theorem BianchiIX.phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNormKernel_derivative_bounds {l a b : ℝ} (hl : 0 < l) (ha : l ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 1 / (2 * l ^ 2) ∧
      |phaseNormKernelDa a b| ≤ 1 / l ^ 3 ∧
      |b * phaseNormKernelDb a b| ≤ 3 * b ^ 2 / (4 * l ^ 4) := by
  have ha0 : 0 < a := hl.trans_le ha
  have hK := phaseNorm_pos (b := b) ha0
  have hKa := phaseNorm_ge (b := b) ha0.le
  have hKl := ha.trans hKa
  have hSl : 2 * l ≤ phaseNorm a b + a := by linarith only [ha, hKl]
  have hS : 0 < phaseNorm a b + a := add_pos hK ha0
  have hprod : 2 * l ^ 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul hKl hSl (by positivity : 0 ≤ 2 * l) hK.le
    nlinarith only [H]
  have hprod2 : 4 * l ^ 4 ≤ phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * l ^ 2) hprod 2
    nlinarith only [H]
  refine ⟨by unfold phaseNormKernel; positivity, ?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hprod
  · rw [phaseNormKernelDa, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos hK 3)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hKl 3)
  · have hid : |b * phaseNormKernelDb a b| =
        b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
      have H : b * phaseNormKernelDb a b =
          -(b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2)) := by
        dsimp [phaseNormKernelDb]
        ring
      rw [H, abs_neg, abs_of_nonneg (by positivity)]
    rw [hid]
    calc
      _ ≤ (b ^ 2 * (3 * phaseNorm a b)) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [hKa]) (sq_nonneg b)
      _ = 3 * b ^ 2 / (phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2) := by field_simp
      _ ≤ 3 * b ^ 2 / (4 * l ^ 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hprod2

end
end

section
noncomputable section
open BianchiIX

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

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_kernel_derivative_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseKernel m v w| ≤ 3 / μ ^ 2 ∧
    |matchingPhaseKernelDm m v w| ≤ 9 / μ ^ 3 ∧
    |matchingPhaseKernelPartials m v w 0| ≤ 12 / μ ^ 3 ∧
    |matchingPhaseKernelPartials m v w 2| ≤ 32 * v ^ 2 / μ ^ 4 ∧
    |matchingPhaseKernelPartials m v w 3| ≤ 32 * w ^ 2 / μ ^ 4 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hp := phaseNormKernel_derivative_bounds (b := v) hμ0
    (show μ ≤ m + 1 by linarith only [(abs_le.mp hm).1])
  have hn := phaseNormKernel_derivative_bounds (b := w)
    (by positivity : 0 < 5 * μ / 8) (show 5 * μ / 8 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hpρ : phaseNormKernel (m + 1) v ≤ 1 / μ ^ 2 := by
    exact hp.2.1.trans (by convert! div_le_div_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 by norm_num) (sq_nonneg μ) using 1; ring)
  have hnρ : phaseNormKernel (m - 1) w ≤ 2 / μ ^ 2 := by
    exact hn.2.1.trans (by convert! div_le_div_of_nonneg_right (show (32 / 25 : ℝ) ≤ 2 by norm_num) (sq_nonneg μ) using 1; ring)
  have hna : |phaseNormKernelDa (m - 1) w| ≤ 8 / μ ^ 3 := by
    exact hn.2.2.1.trans (by convert! div_le_div_of_nonneg_right (show (512 / 125 : ℝ) ≤ 8 by norm_num) (by positivity : 0 ≤ μ ^ 3) using 1; ring)
  have hpq : |v * phaseNormKernelDb (m + 1) v| ≤ 5 * v ^ 2 / μ ^ 4 := by
    apply hp.2.2.2.trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (3 / 4 : ℝ) ≤ 5 by norm_num) (sq_nonneg v))
      (by positivity : 0 ≤ μ ^ 4) using 1
    ring
  have hnq : |w * phaseNormKernelDb (m - 1) w| ≤ 5 * w ^ 2 / μ ^ 4 := by
    apply hn.2.2.2.trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (3072 / 625 : ℝ) ≤ 5 by norm_num) (sq_nonneg w))
      (by positivity : 0 ≤ μ ^ 4) using 1
    ring
  have hRm : |matchingPhaseKernelDm m v w| ≤ 9 / μ ^ 3 :=
    ((abs_sub _ _).trans (add_le_add hp.2.2.1 hna)).trans_eq (by ring)
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have wall_bound (r e : ℝ) (he : |e| ≤ 3 * r ^ 2 / μ) :
      |matchingPhaseKernelDm m v w * e| ≤ 27 * r ^ 2 / μ ^ 4 := by
    rw [abs_mul]
    exact (mul_le_mul hRm he (abs_nonneg _) (by positivity)).trans_eq (by ring)
  refine ⟨?_, hRm, ?_, ?_, ?_⟩
  · change |phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w| ≤ _
    have H := abs_sub (phaseNormKernel (m + 1) v) (phaseNormKernel (m - 1) w)
    rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1] at H
    exact (H.trans (add_le_add hpρ hnρ)).trans_eq (by ring)
  · change |matchingPhaseKernelDm m v w / matchingPhaseSlope m v w| ≤ _
    rw [div_eq_mul_inv, abs_mul]
    have H := mul_le_mul hRm (by simpa only [one_div] using hvar.1) (abs_nonneg _) (by positivity : 0 ≤ 9 / μ ^ 3)
    exact H.trans_eq (by ring)
  · exact ((abs_add_le _ _).trans (add_le_add (wall_bound v _ hvar.2.1) hpq)).trans_eq (by ring)
  · exact ((abs_sub _ _).trans (add_le_add (wall_bound w _ hvar.2.2) hnq)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseB_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseB m u v w| ≤ 6 / μ ^ 3 ∧
    |connectionPhaseBPartials m u v w 0| ≤ 40 / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 1| ≤ 36 * u / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 2| ≤ 100 * v ^ 2 / μ ^ 5 + 12 * u * v / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 3| ≤ 100 * w ^ 2 / μ ^ 5 + 12 * u * w / μ ^ 4 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 := hu.1
  have hK := matchingPhase_kernel_derivative_bounds hμ hm hv hw
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hS := (connection_amplitude_base_bounds hμ hm hu hv hw).2.2.2
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have div_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w| ≤ 2 * K / μ := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD).trans_eq (by ring)
  have div_sq_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w ^ 2| ≤ 4 * K / μ ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hD0 2)]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD2).trans_eq (by ring)
  have wall_bound (r e q : ℝ) (hr : 0 ≤ r) (he : |e| ≤ 3 * r ^ 2 / μ)
      (hq : |q| ≤ 32 * r ^ 2 / μ ^ 4) :
      |q / connectionSpeed m u v w - matchingPhaseKernel m v w * (e - u * r) / connectionSpeed m u v w ^ 2| ≤
        100 * r ^ 2 / μ ^ 5 + 12 * u * r / μ ^ 4 := by
    have hdiff : |e - u * r| ≤ 3 * r ^ 2 / μ + u * r := by
      simpa only [abs_of_nonneg (mul_nonneg hu0 hr)] using (abs_sub e (u * r)).trans (add_le_add he le_rfl)
    have hnum : |matchingPhaseKernel m v w * (e - u * r)| ≤
        (3 / μ ^ 2) * (3 * r ^ 2 / μ + u * r) := by
      rw [abs_mul]
      exact mul_le_mul hK.1 hdiff (abs_nonneg _) (by positivity)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ hq) (div_sq_bound _ _ hnum))).trans_eq (by ring)
  refine ⟨(div_bound _ _ hK.1).trans_eq (by ring), ?_, ?_,
    wall_bound v _ _ hv.1 hvar.2.1 hK.2.2.2.1, wall_bound w _ _ hw.1 hvar.2.2 hK.2.2.2.2⟩
  · have hnum : |matchingPhaseKernel m v w * (1 / matchingPhaseSlope m v w)| ≤ (3 / μ ^ 2) * (4 / 3) := by
      rw [abs_mul]
      exact mul_le_mul hK.1 hvar.1 (abs_nonneg _) (by positivity)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ hK.2.2.1) (div_sq_bound _ _ hnum))).trans_eq (by ring)
  · have hnum : |matchingPhaseKernel m v w * (-u * (v + w - 2 * u))| ≤ (3 / μ ^ 2) * (u * 3) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hu0]
      exact mul_le_mul hK.1 (mul_le_mul_of_nonneg_left hS hu0) (by positivity) (by positivity)
    change |0 / connectionSpeed m u v w - matchingPhaseKernel m v w * (-u * (v + w - 2 * u)) /
      connectionSpeed m u v w ^ 2| ≤ _
    rw [zero_div, zero_sub, abs_neg]
    exact (div_sq_bound _ _ hnum).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_identity {m v w : ℝ} (hm : 1 < m) :
    matchingPhaseWeight m v w = matchingPhase m v w - (m + 1) / phaseNorm (m + 1) v +
      (m - 1) / phaseNorm (m - 1) w := by
  have hp := phaseNorm_pos (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_pos (b := w) (show 0 < m - 1 by linarith only [hm])
  dsimp [matchingPhaseWeight, matchingPhaseSlope, matchingPhase]
  field_simp
  linear_combination -phaseNorm (m - 1) w * phaseNorm_sq (m + 1) v -
    phaseNorm (m + 1) v * phaseNorm_sq (m - 1) w

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_offset {m v w : ℝ} (hm : 1 < m) :
    matchingPhaseWeight m v w - m =
      v ^ 2 * (phaseNorm (m + 1) v + 1) /
        (phaseNorm (m + 1) v * (phaseNorm (m + 1) v + m + 1)) +
      w ^ 2 * (phaseNorm (m - 1) w - 1) /
        (phaseNorm (m - 1) w * (phaseNorm (m - 1) w + m - 1)) := by
  have hp : 0 < m + 1 := by linarith only [hm]
  have hn : 0 < m - 1 := by linarith only [hm]
  rw [matchingPhaseWeight_identity hm]
  calc
    _ = (phaseNorm (m + 1) v - (m + 1)) + (phaseNorm (m - 1) w - (m - 1)) +
        (1 - (m + 1) / phaseNorm (m + 1) v) - (1 - (m - 1) / phaseNorm (m - 1) w) := by
      dsimp [matchingPhase]
      ring
    _ = _ := by
      rw [phaseNorm_defect hp, phaseNorm_defect hn, phaseNorm_ratio_defect hp, phaseNorm_ratio_defect hn]
      have hkp := phaseNorm_pos (b := v) hp
      have hkn := phaseNorm_pos (b := w) hn
      have hsp : 0 < phaseNorm (m + 1) v + m + 1 := by linarith only [hkp, hp]
      have hsn : 0 < phaseNorm (m - 1) w + m - 1 := by linarith only [hkn, hn]
      dsimp [phaseNormKernel]
      field_simp
      ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_offset_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    0 ≤ matchingPhaseWeight m v w - m ∧
      matchingPhaseWeight m v w - m ≤ 8 * (v ^ 2 + w ^ 2) / (5 * μ) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm1 : 1 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hm1])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hm1])
  have term (K a r e l : ℝ) (hl : 0 < l) (hK : l ≤ K) (ha : 0 < a)
      (he0 : 0 ≤ K + e) (he : e ≤ a) :
      0 ≤ r ^ 2 * (K + e) / (K * (K + a)) ∧
        r ^ 2 * (K + e) / (K * (K + a)) ≤ r ^ 2 / l := by
    have hK0 := hl.trans_le hK
    have hS : 0 < K + a := add_pos hK0 ha
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ r ^ 2 * (K + a) / (K * (K + a)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [he]) (sq_nonneg r)
      _ = r ^ 2 / K := by field_simp
      _ ≤ r ^ 2 / l := div_le_div_of_nonneg_left (sq_nonneg r) hl hK
  have hpterm := term (phaseNorm (m + 1) v) (m + 1) v 1 μ hμ0
    (by linarith only [hp, (abs_le.mp hm).1]) (by linarith only [hm1])
    (by linarith only [hp, hm1]) (by linarith only [hm1])
  have hnterm := term (phaseNorm (m - 1) w) (m - 1) w (-1) (5 * μ / 8) (by positivity)
    (by linarith only [hn, hμ, (abs_le.mp hm).1]) (by linarith only [hm1])
    (by linarith only [hn, hμ, (abs_le.mp hm).1]) (by linarith only [hm1])
  have hid := matchingPhaseWeight_offset (v := v) (w := w) hm1
  have hid' : matchingPhaseWeight m v w - m =
      v ^ 2 * (phaseNorm (m + 1) v + 1) / (phaseNorm (m + 1) v * (phaseNorm (m + 1) v + (m + 1))) +
      w ^ 2 * (phaseNorm (m - 1) w + -1) / (phaseNorm (m - 1) w * (phaseNorm (m - 1) w + (m - 1))) := by
    convert! hid using 1
    ring
  rw [hid']
  refine ⟨add_nonneg hpterm.1 hnterm.1, (add_le_add hpterm.2 hnterm.2).trans ?_⟩
  have H := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 8 / 5 by norm_num) (sq_nonneg v)) hμ0.le
  convert! add_le_add H (le_refl (w ^ 2 / (5 * μ / 8))) using 1 <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_sharp_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 < matchingPhaseWeight m v w ∧ matchingPhaseWeight m v w ≤ 3 * μ / 2 ∧
      matchingPhaseWeight m v w - m ≤ 4 / 5 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have H := matchingPhaseWeight_offset_bounds (v := v) (w := w) hμ hm
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hsmall : matchingPhaseWeight m v w - m ≤ 4 / 5 := H.2.trans
    ((div_le_iff₀ (by positivity : 0 < 5 * μ)).mpr (by nlinarith only [hv2, hw2, hμ]))
  refine ⟨?_, ?_, hsmall⟩
  · linarith only [H.1, hμ, (abs_le.mp hm).1]
  · linarith only [hsmall, hμ, (abs_le.mp hm).2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_speed_offset_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ matchingPhaseWeight m v w - connectionSpeed m u v w ∧
      |matchingPhaseWeight m v w - connectionSpeed m u v w| ≤ 2 := by
  have Hoff := matchingPhaseWeight_offset_bounds (v := v) (w := w) hμ hm
  have Hsmall := (matchingPhaseWeight_sharp_bounds hμ hm hv hw).2.2
  have HC := connection_coupling_bounds hu.1 hv hw
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hlow : 0 ≤ matchingPhaseWeight m v w - connectionSpeed m u v w := by
    dsimp [connectionSpeed]
    nlinarith only [Hoff.1, HC.1, hu2]
  refine ⟨hlow, ?_⟩
  rw [abs_of_nonneg hlow]
  dsimp [connectionSpeed]
  linarith only [Hsmall, HC.2, hu.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseRemainder_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseRemainder m u v w| ≤ 6 := by
  have hf := matchingPhase_slope_bounds hμ hm hv hw
  have hf0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hf.1]
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 5 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have hH := (matchingPhaseWeight_speed_offset_bounds hμ hm hu hv hw).2
  have H1 : |matchingPhaseSlope m v w * (v - w)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hf0]
    exact (mul_le_mul hf.2 hd (abs_nonneg _) zero_le_one).trans_eq (by ring)
  have H2 : |(v + w - u) * (matchingPhaseWeight m v w - connectionSpeed m u v w)| ≤ 5 := by
    rw [abs_mul]
    exact (mul_le_mul hS hH (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact ((abs_add_le _ _).trans (add_le_add H1 H2)).trans_eq (by norm_num)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseRemainder_phase_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w| ≤ 20 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have haux := matchingPhase_auxiliary_m_bounds (v := v) (w := w) hμ hm
  have hvar := (matchingPhase_inverse_weighted_bounds hμ hm hv hw).1
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have H1 : |matchingPhaseSlopeDm m v w * (v - w)| ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) := by
    rw [abs_mul, abs_of_nonneg haux.1]
    exact (mul_le_mul haux.2.1 hd (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have H2 : |(v + w - u) * (matchingPhaseWeightDm m v w - 1)| ≤ 6 * (v ^ 2 + w ^ 2) / μ ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hS haux.2.2 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have HN := (abs_add_le _ _).trans (add_le_add H1 H2)
  change |connectionPhaseRemainderDm m u v w| ≤ _ at HN
  rw [div_eq_mul_inv, abs_mul]
  calc
    _ ≤ (9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) + 6 * (v ^ 2 + w ^ 2) / μ ^ 2) * (4 / 3) :=
      mul_le_mul HN (by simpa only [one_div] using hvar) (abs_nonneg _) (by positivity)
    _ = (6 / μ ^ 3 + 8 / μ ^ 2) * (v ^ 2 + w ^ 2) := by ring
    _ ≤ (6 / μ ^ 3 + 8 / μ ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hv2, hw2]) (by positivity)
    _ = (12 + 16 * μ) / μ ^ 3 := by field_simp; ring
    _ ≤ (20 * μ) / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 20 / μ ^ 2 := by field_simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionPhaseAJ_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseAJ m u v w| ≤ 48 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have hN := connectionPhaseRemainder_bound hμ hm hu hv hw
  have hNJ := connectionPhaseRemainder_phase_bound hμ hm hu hv hw
  have hf := (matchingPhase_inverse_weighted_bounds hμ hm hv hw).1
  have hfirst : |(connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) /
      connectionSpeed m u v w| ≤ 40 / μ ^ 3 := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ (by positivity) hNJ (by positivity) hD).trans_eq (by ring)
  have hsecond : |(connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) /
      connectionSpeed m u v w ^ 2| ≤ 32 / μ ^ 2 := by
    have H : |connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)| ≤ 8 := by
      rw [abs_mul]
      exact (mul_le_mul hN hf (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [abs_div, abs_of_pos (pow_pos hD0 2)]
    exact (div_le_div₀ (by norm_num) H (by positivity) hD2).trans_eq (by ring)
  have hid : connectionPhaseAJ m u v w =
      -((connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) / connectionSpeed m u v w) +
      (connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) / connectionSpeed m u v w ^ 2 := by
    dsimp [connectionPhaseAJ]
    ring
  rw [hid]
  have H := abs_add_le (-((connectionPhaseRemainderDm m u v w / matchingPhaseSlope m v w) /
    connectionSpeed m u v w)) ((connectionPhaseRemainder m u v w * (1 / matchingPhaseSlope m v w)) / connectionSpeed m u v w ^ 2)
  rw [abs_neg] at H
  calc
    _ ≤ 40 / μ ^ 3 + 32 / μ ^ 2 := H.trans (add_le_add hfirst hsecond)
    _ = (40 + 32 * μ) / μ ^ 3 := by field_simp
    _ ≤ (48 * μ) / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [hμ]) (by positivity)
    _ = 48 / μ ^ 2 := by field_simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionPhaseGJ_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseGJ m u v w| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hA := connectionPhaseAJ_bound hμ hm hu hv hw
  have hB := (connectionPhaseB_bounds hμ hm hu hv hw).2.1
  have H1 : |u * connectionPhaseAJ m u v w| ≤ u * (48 / μ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left hA hu.1
  have H2 : |(v * w) ^ 2 * connectionPhaseBPartials m u v w 0| ≤ (v * w) ^ 2 * (40 / μ ^ 4) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  apply ((abs_add_le _ _).trans (add_le_add H1 H2)).trans
  have huq : 0 ≤ u / μ ^ 2 := div_nonneg hu.1 (sq_nonneg μ)
  have hpq : 0 ≤ (v * w) ^ 2 / μ ^ 4 := by positivity
  calc
    _ = 48 * (u / μ ^ 2) + 40 * ((v * w) ^ 2 / μ ^ 4) := by ring
    _ ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) := by linarith only [huq, hpq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseAPartials_phase {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    connectionPhaseAPartials m u v w 0 = connectionPhaseAJ m u v w := by
  dsimp [connectionPhaseAPartials, connectionPhaseNumeratorPartials, matchingPhaseSlopePartials,
    matchingPhaseWeightPartials, connectionSpeedPartials, connectionPhaseAJ,
    connectionPhaseRemainderDm, connectionPhaseRemainder, connectionPhaseA]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionPhaseGPartials_phase {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    connectionPhaseGPartials m u v w 0 = connectionPhaseGJ m u v w := by
  simp only [connectionPhaseGPartials, Matrix.cons_val_zero, add_zero, connectionPhaseAPartials_phase hD]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseNumerator_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseNumerator m u v w| ≤ 4 * μ ∧
    |connectionPhaseNumeratorPartials m u v w 1| ≤ 3 * μ / 2 * u ∧
    |connectionPhaseNumeratorPartials m u v w 2| ≤ 3 * μ * v ∧
    |connectionPhaseNumeratorPartials m u v w 3| ≤ 3 * μ * w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hf := matchingPhase_slope_bounds hμ hm hv hw
  have hf0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hf.1]
  have hH := matchingPhaseWeight_sharp_bounds hμ hm hv hw
  have hwall := matchingPhase_wall_bounds hμ hm hv hw
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hS : |v + w - u| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2, hu.1, hu.2]
  have fmul (r : ℝ) (hr : 0 ≤ r) : |matchingPhaseSlope m v w * r| ≤ r := by
    rw [abs_mul, abs_of_nonneg hf0, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_right hf.2 hr).trans_eq (by ring)
  have wall_bound (r p q e : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
      (hp : |p| ≤ 5 * r ^ 2 / μ ^ 2) (hq : |q| ≤ 5 * r ^ 2 / μ ^ 2) (he : |e| ≤ r) :
      |p * (v - w) + e + r * matchingPhaseWeight m v w + (v + w - u) * q| ≤ 3 * μ * r := by
    have H1 : |p * (v - w)| ≤ 5 * r ^ 2 / μ ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hp hd (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have H2 : |r * matchingPhaseWeight m v w| ≤ r * (3 * μ / 2) := by
      rw [abs_mul, abs_of_nonneg hr.1, abs_of_pos hH.1]
      exact mul_le_mul_of_nonneg_left hH.2.1 hr.1
    have H3 : |(v + w - u) * q| ≤ 10 * r ^ 2 / μ ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hS hq (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have H := ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add ((abs_add_le _ _).trans (add_le_add H1 he)) H2) H3)
    have hr2 : r ^ 2 ≤ r := by nlinarith only [hr.1, hr.2, mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    have hsmall : r ^ 2 / μ ^ 2 ≤ r / 16 := div_le_div₀ hr.1 hr2 (by norm_num) hμ2
    have hcoef := mul_le_mul_of_nonneg_right (show (15 / 16 : ℝ) + 1 ≤ 3 * μ / 2 by linarith only [hμ]) hr.1
    calc
      _ ≤ 15 * (r ^ 2 / μ ^ 2) + r + r * (3 * μ / 2) := H.trans_eq (by ring)
      _ ≤ 3 * μ * r := by linarith only [mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 15), hcoef]
  refine ⟨?_, ?_, wall_bound v _ _ _ hv hwall.1 hwall.2.2.1 (fmul v hv.1), ?_⟩
  · have H1 : |matchingPhaseSlope m v w * (v - w)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact (mul_le_mul hf.2 hd (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have H2 : |(v + w - u) * matchingPhaseWeight m v w| ≤ 3 * μ := by
      rw [abs_mul, abs_of_pos hH.1]
      exact (mul_le_mul hS hH.2.1 hH.1.le (by norm_num)).trans_eq (by ring)
    exact ((abs_add_le _ _).trans (add_le_add H1 H2)).trans (by linarith only [hμ])
  · change |-u * matchingPhaseWeight m v w| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg hu.1, abs_of_pos hH.1]
    exact (mul_le_mul_of_nonneg_left hH.2.1 hu.1).trans_eq (by ring)
  · have He : |-matchingPhaseSlope m v w * w| ≤ w := by simpa only [neg_mul, abs_neg] using fmul w hw.1
    change |matchingPhaseSlopePartials m v w 3 * (v - w) - matchingPhaseSlope m v w * w +
      w * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 3| ≤ _
    simpa only [sub_eq_add_neg, neg_mul] using wall_bound w _ _ _ hw hwall.2.1 hwall.2.2.2 He

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseA_wall_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseA m u v w| ≤ 8 ∧
    |connectionPhaseAPartials m u v w 1| ≤ 16 * u ∧
    |connectionPhaseAPartials m u v w 2| ≤ 16 * v ∧
    |connectionPhaseAPartials m u v w 3| ≤ 16 * w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hu1 : u ≤ 1 := by linarith only [hu.2]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hN := connectionPhaseNumerator_bounds hμ hm hu hv hw
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have div_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w| ≤ 2 * K / μ := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD).trans_eq (by ring)
  have hA : |connectionPhaseA m u v w| ≤ 8 := by
    change |-connectionPhaseNumerator m u v w / connectionSpeed m u v w| ≤ _
    exact (div_bound _ _ (by simpa only [abs_neg] using hN.1)).trans_eq (by field_simp; norm_num)
  have column (n e K L : ℝ) (hn : |n| ≤ K) (he : |e| ≤ L) :
      |-n / connectionSpeed m u v w - connectionPhaseA m u v w * e / connectionSpeed m u v w| ≤
        2 * (K + 8 * L) / μ := by
    have H : |connectionPhaseA m u v w * e| ≤ 8 * L := by
      rw [abs_mul]
      exact mul_le_mul hA he (abs_nonneg _) (by norm_num)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ (by simpa only [abs_neg] using hn))
      (div_bound _ _ H))).trans_eq (by ring)
  have wall_bound (r n e : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (hn : |n| ≤ 3 * μ * r)
      (he : |e| ≤ 3 * r ^ 2 / μ) :
      |-n / connectionSpeed m u v w - connectionPhaseA m u v w * (e - u * r) / connectionSpeed m u v w| ≤ 16 * r := by
    have he' : |e - u * r| ≤ 3 * r ^ 2 / μ + u * r := by
      simpa only [abs_of_nonneg (mul_nonneg hu0 hr.1)] using (abs_sub e (u * r)).trans (add_le_add he le_rfl)
    have hr2 : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    have H1 : r ^ 2 / μ ^ 2 ≤ r / 16 := div_le_div₀ hr.1 hr2 (by norm_num) hμ2
    have H2 : u * r / μ ≤ r / 4 := div_le_div₀ hr.1
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 hr.1) (by norm_num) hμ
    calc
      _ ≤ 2 * (3 * μ * r + 8 * (3 * r ^ 2 / μ + u * r)) / μ := column _ _ _ _ hn he'
      _ = 6 * r + 48 * (r ^ 2 / μ ^ 2) + 16 * (u * r / μ) := by field_simp; ring
      _ ≤ 16 * r := by linarith only [H1, H2, hr.1]
  refine ⟨hA, ?_, wall_bound v _ _ hv hN.2.2.1 hvar.2.1, wall_bound w _ _ hw hN.2.2.2 hvar.2.2⟩
  · have hS := (connection_amplitude_base_bounds hμ hm hu hv hw).2.2.2
    have he : |-u * (v + w - 2 * u)| ≤ 3 * u := by
      rw [abs_mul, abs_neg, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left hS hu0).trans_eq (by ring)
    have H : u / μ ≤ u / 4 := div_le_div_of_nonneg_left hu0 (by norm_num) hμ
    calc
      _ ≤ 2 * (3 * μ / 2 * u + 8 * (3 * u)) / μ := column _ _ _ _ hN.2.1 he
      _ = 3 * u + 48 * (u / μ) := by field_simp; ring
      _ ≤ 16 * u := by linarith only [H, hu0]

end
end

theorem solution {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseGPartials m u v w 0| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) ∧
    |connectionPhaseGPartials m u v w 1| ≤ 32 * u ∧
    |connectionPhaseGPartials m u v w 2| ≤ 32 * (u * v + (v * w) ^ 2 / μ ^ 3) ∧
    |connectionPhaseGPartials m u v w 3| ≤ 32 * (u * w + (v * w) ^ 2 / μ ^ 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hu1 : u ≤ 1 := by linarith only [hu.2]
  have hu2 : u ^ 2 ≤ u := by nlinarith only [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ4 : 36 ≤ μ ^ 4 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 4
    norm_num at H
    linarith only [H]
  have hA := connectionPhaseA_wall_bounds hμ hm hu hv hw
  have hB := connectionPhaseB_bounds hμ hm hu hv hw
  have hP0 : 0 ≤ (v * w) ^ 2 := sq_nonneg _
  have hP : (v * w) ^ 2 ≤ 1 := by
    have H : 0 ≤ v * w ∧ v * w ≤ 1 := ⟨mul_nonneg hv.1 hw.1,
      (mul_le_mul hv.2 hw.2 hw.1 zero_le_one).trans_eq (by norm_num)⟩
    simpa using pow_le_pow_left₀ H.1 H.2 2
  have wall_bound (r a b : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (ha : |a| ≤ 16 * r)
      (hb : |b| ≤ 100 * r ^ 2 / μ ^ 5 + 12 * u * r / μ ^ 4) :
      |u * a + (v * w) ^ 2 * b + 2 * (v * w) ^ 2 * connectionPhaseB m u v w| ≤
        32 * (u * r + (v * w) ^ 2 / μ ^ 3) := by
    have hr2 : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr.1 hr.2 2
    have hur : u * r ≤ 1 := (mul_le_mul hu1 hr.2 hr.1 zero_le_one).trans_eq (by norm_num)
    have H1 : r ^ 2 / μ ^ 2 ≤ 1 / 16 := div_le_div₀ zero_le_one hr2 (by norm_num) hμ2
    have H2 : u * r / μ ≤ 1 / 4 := div_le_div₀ zero_le_one hur (by norm_num) hμ
    have hb' : |b| ≤ 20 / μ ^ 3 := hb.trans (by
      calc
        _ = (100 * (r ^ 2 / μ ^ 2) + 12 * (u * r / μ)) / μ ^ 3 := by field_simp
        _ ≤ 20 / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [H1, H2]) (by positivity))
    have Ha : |u * a| ≤ 16 * (u * r) := by
      rw [abs_mul, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left ha hu0).trans_eq (by ring)
    have Hb : |(v * w) ^ 2 * b| ≤ 20 * ((v * w) ^ 2 / μ ^ 3) := by
      rw [abs_mul, abs_of_nonneg hP0]
      exact (mul_le_mul_of_nonneg_left hb' hP0).trans_eq (by ring)
    have HB : |2 * (v * w) ^ 2 * connectionPhaseB m u v w| ≤ 12 * ((v * w) ^ 2 / μ ^ 3) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (v * w) ^ 2)]
      exact (mul_le_mul_of_nonneg_left hB.1 (by positivity : 0 ≤ 2 * (v * w) ^ 2)).trans_eq (by ring)
    have H := ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add Ha Hb) HB)
    exact H.trans (by nlinarith only [mul_nonneg hu0 hr.1])
  refine ⟨?_, ?_, wall_bound v _ _ hv hA.2.2.1 hB.2.2.2.1,
    wall_bound w _ _ hw hA.2.2.2 hB.2.2.2.2⟩
  · have hD := (connection_speed_bounds hμ hm hu hv hw).1
    rw [connectionPhaseGPartials_phase (by linarith only [hD, hμ])]
    exact connectionPhaseGJ_bound hμ hm hu hv hw
  · have H1 : |u * connectionPhaseAPartials m u v w 1| ≤ 16 * u := by
      rw [abs_mul, abs_of_nonneg hu0]
      have H := mul_le_mul_of_nonneg_left hA.2.1 hu0
      nlinarith only [H, hu2]
    have H2 : |(v * w) ^ 2 * connectionPhaseBPartials m u v w 1| ≤ u := by
      rw [abs_mul, abs_of_nonneg hP0]
      have H : 36 * u / μ ^ 4 ≤ u := by
        calc
          _ = u * (36 / μ ^ 4) := by ring
          _ ≤ u * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hμ4) hu0
          _ = u := mul_one u
      exact (mul_le_mul hP (hB.2.2.1.trans H) (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have H3 : |u * connectionPhaseA m u v w| ≤ 8 * u := by
      rw [abs_mul, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left hA.1 hu0).trans_eq (by ring)
    exact (((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add H1 H2) H3)).trans (by linarith only [hu0])
