-- Prove2me | solution 1 for BianchiIX.connectionLog_matchingPhase_drift
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:23.242201+00:00
-- url     : https://prove2.me/submissions/2adc0259-91e6-497a-8f7c-cf746cd3cf0a

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionLog_prefix_integrals
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set MeasureTheory

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

private theorem BianchiIX.connection_coupling_nonneg {u v w : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huv : u ≤ v) : 0 ≤ coupling u v w := by
  unfold coupling
  exact mul_nonneg hu (by linarith only [hw, huv])

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

private theorem BianchiIX.matchingPhase_interaction {m v w : ℝ} (hm : 1 < m) :
    v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
      w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) = (v * w) ^ 2 * matchingPhaseKernel m v w := by
  have hp := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_ratio_defect (b := w) (show 0 < m - 1 by linarith only [hm])
  have hn' : (m - 1) / phaseNorm (m - 1) w - 1 = -(w ^ 2 * phaseNormKernel (m - 1) w) := by
    linarith only [hn]
  rw [hp, hn']
  unfold matchingPhaseKernel
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_directional {m u v w : ℝ} (hm : 1 < m) :
    matchingPhaseSlope m v w * (-phaseVelocity (-m) u v w) +
      v / phaseNorm (m + 1) v * activeVelocity (-m) u v w +
      w / phaseNorm (m - 1) w * weakVelocity (-m) u v w = matchingPhaseRate m u v w := by
  calc
    _ = v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
        w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) -
        u * matchingPhaseSlope m v w * (v - w) - coupling u v w * matchingPhaseWeight m v w := by
      dsimp [matchingPhaseSlope, matchingPhaseWeight, phaseVelocity, activeVelocity, weakVelocity]
      ring
    _ = _ := by rw [matchingPhase_interaction hm]; rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s))
      (matchingPhaseSlope (m t) (v t) (w t) * m' +
        v t / phaseNorm (m t + 1) (v t) * v' + w t / phaseNorm (m t - 1) (w t) * w') t := by
  have hp : (m t + 1) ^ 2 + v t ^ 2 ≠ 0 := by
    have H : 0 < m t + 1 := by linarith only [hmt]
    positivity
  have hn : (m t - 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have H : 0 < m t - 1 := by linarith only [hmt]
    positivity
  have H := ((((hm.add_const 1).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub_const 1).pow 2).add (hw.pow 2)).sqrt hn)
  convert! H.sub hm using 1
  dsimp [matchingPhaseSlope, phaseNorm]
  ring

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

private theorem BianchiIX.phaseNormKernel_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 2 / μ ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hn := phaseNorm_pos (b := b) ha0
  have hna := phaseNorm_ge (b := b) ha0.le
  have hprod : μ ^ 2 / 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul (ha.trans hna) (show μ ≤ phaseNorm a b + a by linarith only [ha, hna])
      hμ.le hn.le
    nlinarith only [H]
  have hd : 0 < phaseNorm a b * (phaseNorm a b + a) := mul_pos hn (add_pos hn ha0)
  refine ⟨by unfold phaseNormKernel; positivity, ?_⟩
  have H := one_div_le_one_div_of_le (by positivity : 0 < μ ^ 2 / 2) hprod
  exact H.trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_kernel_bound {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    |matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hp := phaseNormKernel_bounds (b := v) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m + 1)
  have hn := phaseNormKernel_bounds (b := w) hμ0 (by linarith only [hμ, (abs_le.mp hm).1] : μ / 2 ≤ m - 1)
  have H := abs_sub (phaseNormKernel (m + 1) v) (phaseNormKernel (m - 1) w)
  rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1] at H
  change |phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w| ≤ _
  exact (H.trans (add_le_add hp.2 hn.2)).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_weight_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ matchingPhaseWeight m v w ∧ matchingPhaseWeight m v w ≤ 2 * μ := by
  have hm0 : 0 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hp := phaseNorm_ge (b := v) (show 0 ≤ m + 1 by linarith only [hm0])
  have hn := phaseNorm_ge (b := w) (show 0 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hp0 : 0 < phaseNorm (m + 1) v := by linarith only [hp, hm0]
  have hn0 : 0 < phaseNorm (m - 1) w := by linarith only [hn, hμ, (abs_le.mp hm).1]
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  have hvq : v ^ 2 / phaseNorm (m + 1) v ≤ 1 :=
    (div_le_one hp0).mpr (by linarith only [hv2, hp, hm0])
  have hwq : w ^ 2 / phaseNorm (m - 1) w ≤ 1 :=
    (div_le_one hn0).mpr (by linarith only [hw2, hn, hμ, (abs_le.mp hm).1])
  have hprod := mul_le_mul_of_nonneg_left hS.2 hm0.le
  dsimp [matchingPhaseWeight]
  constructor
  · positivity
  · linarith only [hprod, hvq, hwq, hμ, (abs_le.mp hm).2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_rate_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseRate m u v w| ≤ 5 * μ * u + 4 / μ ^ 2 * (v * w) ^ 2 := by
  have hS := matchingPhase_slope_bounds hμ hm hv hw
  have hS0 : 0 ≤ matchingPhaseSlope m v w := by linarith only [hS.1]
  have hH := matchingPhase_weight_bounds hμ hm hv hw
  have hR := matchingPhase_kernel_bound (v := v) (w := w) hμ hm
  have hC := connection_coupling_bounds hu.1 hv hw
  have hCabs : |coupling u v w| ≤ 2 * u := by
    apply abs_le.mpr
    have H := mul_le_mul_of_nonneg_left (show u ≤ 2 by linarith only [hu.2]) hu.1
    constructor <;> nlinarith only [H, hC.1, hC.2]
  have hdiff : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hfirst : |u * matchingPhaseSlope m v w * (v - w)| ≤ u := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu.1, abs_of_nonneg hS0]
    have H := mul_le_mul (mul_le_mul_of_nonneg_left hS.2 hu.1) hdiff (abs_nonneg _)
      (mul_nonneg hu.1 zero_le_one)
    simpa only [mul_one] using H
  have hsecond : |coupling u v w * matchingPhaseWeight m v w| ≤ 4 * μ * u := by
    rw [abs_mul, abs_of_nonneg hH.1]
    have H := mul_le_mul hCabs hH.2 hH.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.1)
    nlinarith only [H]
  have hthird : |(v * w) ^ 2 * matchingPhaseKernel m v w| ≤ 4 / μ ^ 2 * (v * w) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hR (sq_nonneg _)).trans_eq (mul_comm _ _)
  have H := (abs_sub ((v * w) ^ 2 * matchingPhaseKernel m v w - u * matchingPhaseSlope m v w * (v - w))
    (coupling u v w * matchingPhaseWeight m v w)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  change |matchingPhaseRate m u v w| ≤ _ at H
  have huμ := mul_le_mul_of_nonneg_right (show 1 ≤ μ by linarith only [hμ]) hu.1
  nlinarith only [H, hfirst, hsecond, hthird, huμ]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_connectionLog_product {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z) (hD : connectionClockRate (Y z) ≠ 0) :
    HasDerivAt (fun t => Y t 2 * Y t 3)
      ((-2 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) / connectionClockRate (Y z)) * (Y z 2 * Y z 3)) z := by
  have H := (hasDerivAt_pi.mp hY 2).mul (hasDerivAt_pi.mp hY 3)
  rw [(connectionLogField_components hD).2.2.1, (connectionLogField_components hD).2.2.2] at H
  convert! H using 1
  dsimp [connectionClockRate, connectionSpeed] at *
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (a * matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
    (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  simp only [Pi.neg_apply] at H
  have hrate := matchingPhase_directional (u := Y t 1) (v := Y t 2) (w := Y t 3) hm
  simp only [neg_neg] at hrate
  convert! H using 1
  rw [← hrate]
  change a * _ = matchingPhaseSlope _ _ _ * (-(a * phaseVelocity _ _ _ _)) +
    _ * (a * activeVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_connectionLog {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3) / connectionClockRate (Y t)) t := by
  convert! hasDerivAt_matchingPhase_scaled hY hm using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_product_integral {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 / connectionClockRate (Y z)) ≤ (Y a 2 * Y a 3) ^ 2 / 4 := by
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hc (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD := (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  apply integral_le_of_dissipation hab (by norm_num : (0 : ℝ) < 4)
    (fun z hz => (hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz))).pow 2)
    (((hc 2).mul (hc 3) |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))) ?_ (sq_nonneg _)
  intro z hz
  have hC := connection_coupling_nonneg (hu z hz).1 (hw z hz).1 (huv z hz)
  have H := mul_nonneg hC (sq_nonneg (Y z 2 * Y z 3))
  have H' : -4 * (1 + coupling (Y z 1) (Y z 2) (Y z 3)) * (Y z 2 * Y z 3) ^ 2 ≤
      -4 * (Y z 2 * Y z 3) ^ 2 := by nlinarith only [H]
  simp only [Pi.div_apply, Pi.pow_apply, Pi.mul_apply, Function.comp_apply]
  convert! div_le_div_of_nonneg_right H' (hD z hz).le using 1 <;> ring

end
end


/-- A time-independent matching-phase error follows from two dissipative budgets. -/
theorem solution {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    |matchingPhase (-Y b 0) (Y b 2) (Y b 3) - matchingPhase (-Y a 0) (Y a 2) (Y a 3)| ≤
      20 * Y a 1 / μ + (Y a 2 * Y a 3) ^ 2 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hc (i : Fin 4) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hcD := (contDiff_connectionClockRate 1).continuous.comp_continuousOn (HasDerivAt.continuousOn hY)
  let U := fun z => Y z 1 / connectionClockRate (Y z)
  let P := fun z => (Y z 2 * Y z 3) ^ 2 / connectionClockRate (Y z)
  have hU : ContinuousOn U (Icc a b) := (hc 1).div hcD (fun z hz => ne_of_gt (hD z hz))
  have hP : ContinuousOn P (Icc a b) := ((hc 2).mul (hc 3) |>.pow 2).div hcD (fun z hz => ne_of_gt (hD z hz))
  have H := abs_sub_le_integral_bound hab
    (fun z hz => hasDerivAt_matchingPhase_connectionLog (hY z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]))
    ((hU.const_mul (5 * μ)).add (hP.const_mul (4 / μ ^ 2))) (fun z hz => ?_)
  · have hiU := hU.intervalIntegrable_of_Icc (μ := volume) hab
    have hiP := hP.intervalIntegrable_of_Icc (μ := volume) hab
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add (hiU.const_mul (5 * μ)) (hiP.const_mul (4 / μ ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
    have hUb := (connectionLog_prefix_integrals hab hμ hY hm hu hv hw hentry).2.2
    have hPb := connectionLog_product_integral hab hμ hY hm hu hv hw hentry
    have hsum := add_le_add (mul_le_mul_of_nonneg_left hUb (show 0 ≤ 5 * μ by positivity))
      (mul_le_mul_of_nonneg_left hPb (show 0 ≤ 4 / μ ^ 2 by positivity))
    apply (H.trans hsum).trans_eq
    field_simp
    ring
  · rw [abs_div, abs_of_pos (hD z hz)]
    have H := matchingPhase_rate_bound hμ (hm z hz) (hu z hz) ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz)
    exact (div_le_div_of_nonneg_right H (hD z hz).le).trans_eq (by dsimp [U, P]; ring)
