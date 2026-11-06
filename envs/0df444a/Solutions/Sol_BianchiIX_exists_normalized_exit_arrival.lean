-- Prove2me | solution 1 for BianchiIX.exists_normalized_exit_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:04:39.216518+00:00
-- url     : https://prove2.me/submissions/762be2c4-bb4b-43c0-bd5e-dada11c994f7

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_normalized_exit_prefix_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalized_exit_local_prefix
import Theorems.Thm_BianchiIX_projectiveDenom_eq
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exp_neg_exitTailLength {η α : ℝ} (hη : 0 < η) (hα : 0 < α) (J : ℕ) :
    Real.exp (-exitTailLength η α J) = η * α ^ J := by
  simp only [exitTailLength, one_div, Real.log_inv]
  rw [show -(-Real.log η + (J : ℝ) * -Real.log α) = Real.log η + J * Real.log α by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hη, Real.exp_log hα]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_nonneg {η α : ℝ} (hη : 0 < η ∧ η ≤ 1) (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    0 ≤ exitTailLength η α J := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  exact add_nonneg he (mul_nonneg (Nat.cast_nonneg _) ha)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_exitLog_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : β t 2 ≠ 0) :
    HasDerivAt (fun s => -Real.log (β s 2)) (a * exitClockRate (β t)) t := by
  have H := ((hasDerivAt_pi.mp hβ 2).log hv).neg
  convert! H using 1
  change a * exitClockRate (β t) = -(a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) / β t 2)
  dsimp [exitClockRate, activeVelocity]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.isClosed_exitPhysicalRegion (h : ℝ) : IsClosed {y | exitPhysicalRegion h y} := by
  have hr : Continuous (fun y : ProjectiveState => coreRadius (y 0) (y 2)) := by
    unfold coreRadius coreEnergy
    fun_prop
  exact (isClosed_le (continuous_apply 0) continuous_const).inter
    (((isClosed_le continuous_const hr).inter (isClosed_le hr continuous_const)).inter
      ((isClosed_le (continuous_apply 1).abs continuous_const).inter
        (((isClosed_le continuous_const (continuous_apply 2)).inter
          (isClosed_le (continuous_apply 2) continuous_const)).inter
          (isClosed_le (continuous_apply 3).abs continuous_const))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_phase_bounds {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : -5 ≤ y 0 ∧ y 0 < 0 := by
  have hR0 : 0 ≤ coreRadius (y 0) (y 2) := Real.sqrt_nonneg _
  have he := coreRadius_sq (y 0) (y 2)
  dsimp only [coreEnergy] at he
  have hR2 := (sq_le_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 17 / 4)).mpr hy.2.1.2
  have hv0 : 0 ≤ y 2 := (hh.trans_le hy.2.2.2.1.1).le
  constructor
  · nlinarith only [he, hR2, sq_nonneg (y 2)]
  · by_contra hn
    have hm0 : y 0 = 0 := le_antisymm hy.1 (le_of_not_gt hn)
    nlinarith only [he, hm0, hv0, hy.2.2.2.1.2, hy.2.1.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_denom {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 0 < projectiveStateDenom y ∧ projectiveStateDenom y ≤ 48 := by
  have hm := exitPhysicalRegion_phase_bounds hh hy
  have hm2 : (y 0) ^ 2 ≤ 25 := by nlinarith only [hm.1, hm.2]
  have hu := abs_le.mp hy.2.2.1
  have hw := abs_le.mp hy.2.2.2.2
  have hv : 0 ≤ y 2 ∧ y 2 ≤ 1 := ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩
  have hu2 : (y 1) ^ 2 ≤ 1 := by nlinarith only [hu.1, hu.2]
  have hvw : |y 2 - y 3| ≤ 2 := by
    have H := abs_sub (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hvw2 : (y 2 - y 3) ^ 2 ≤ 4 := by nlinarith only [hvw, abs_nonneg (y 2 - y 3), sq_abs (y 2 - y 3)]
  have hsum : |y 2 + y 3| ≤ 2 := by
    have H := abs_add_le (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hc : |2 * y 1 * (y 2 + y 3)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul hy.2.2.1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith only [H]
  change 0 < projectiveDenom (y 0) (y 1) (y 2) (y 3) ∧ projectiveDenom (y 0) (y 1) (y 2) (y 3) ≤ 48
  rw [projectiveDenom_eq]
  constructor
  · nlinarith only [(abs_le.mp hc).2, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2 - y 3)]
  · nlinarith only [(abs_le.mp hc).1, hm2, hu2, hvw2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_exit_chart_lower {x : NormalizedState} {h : ℝ} (hh : 0 < h)
    (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : exitPhysicalRegion h (toProjectiveState x)) : 1 / 8 ≤ 1 + x 0 := by
  have hD := exitPhysicalRegion_denom hh hy
  have H := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
  rw [← H]
  exact (le_div_iff₀ hD.1).mpr (by linarith only [hD.2])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_exit_residence {x : NormalizedState} {t₀ s t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) → β s 2 = 1 →
    (t - s) / 16 ≤ -Real.log (β t 2) ∧ t - s ≤ 16 * Real.log (1 / h) := by
  intro β hregion hV
  let z := fun u => -Real.log (β u 2)
  let q := fun u => (1 + normalizedMaxCurve x t₀ u 0) * exitClockRate (β u)
  have hz (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt z (q u) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)
    exact hasDerivAt_exitLog_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hu)) H.2.1)
      (ne_of_gt (hh.trans_le (hregion u hu).2.2.2.1.1))
  have hq (u : ℝ) (hu : u ∈ Icc s t) : 1 / 16 ≤ q u := by
    have HA := normalized_exit_chart_lower hh (ne_of_gt (hA u hu))
      (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).2.1 (hregion u hu)
    have HD := exitPhysicalRegion_clock hh (hregion u hu)
    have H := mul_le_mul HA HD (by norm_num : (0 : ℝ) ≤ 1 / 2) (hA u hu).le
    change 1 / 16 ≤ (1 + normalizedMaxCurve x t₀ u 0) * exitClockRate (β u)
    nlinarith only [H]
  have H := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hu => (hz u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hz u (interior_subset hu)).deriv]; exact hq u (interior_subset hu))
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have H' : (t - s) / 16 ≤ -Real.log (β t 2) := by
    change 1 / 16 * (t - s) ≤ -Real.log (β t 2) - -Real.log (β s 2) at H
    simpa only [hV, Real.log_one, neg_zero, sub_zero, one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have HL := Real.log_le_log hh (hregion t ⟨hst, le_rfl⟩).2.2.2.1.1
  rw [one_div, Real.log_inv]
  linarith only [H', HL]

end
end

private theorem BianchiIX.isClosed_normalized_exit_times {x : NormalizedState} {t₀ s T h : ℝ}
    (hc : stateConstraint x = 1) (hs : t₀ ≤ s) :
    IsClosed ({u | 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
      exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ u))} ∩ Icc s T) := by
  let a := fun u => 1 + normalizedMaxCurve x t₀ u 0
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  have hα (u : ℝ) (hu : u ∈ Icc s T) :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun u hu =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα u hu))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {u | (1 : ℝ) / 16 ≤ a u}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hβ : ContinuousOn β (Icc s T ∩ {u | (1 : ℝ) / 16 ≤ a u}) := by
    intro u hu
    have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 := lt_of_lt_of_le (by norm_num) hu.2
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt hAu)).continuousAt.comp (hα u hu.1)).continuousWithinAt
  have H := hβ.preimage_isClosed_of_isClosed hD (isClosed_exitPhysicalRegion h)
  convert! H using 1
  ext u
  change (1 / 16 ≤ a u ∧ exitPhysicalRegion h (β u)) ∧ u ∈ Icc s T ↔
    (u ∈ Icc s T ∧ 1 / 16 ≤ a u) ∧ exitPhysicalRegion h (β u)
  tauto


/-- The exact signed Einstein flow reaches the parameter-dependent exit height. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s α b : ℝ),
      stateConstraint x = 1 → t₀ ≤ s → (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      0 < 1 + normalizedMaxCurve x t₀ s 0 →
      let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
      β s 0 < 0 → β s 2 = 1 → coreRadius (β s 0) (β s 2) = 2 + 2 * α →
      |β s 1| + |β s 3| ≤ b →
      ∃ t > s, β t 2 = η * α ^ J ∧
        (∀ u ∈ Icc s t, 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
          exitPhysicalRegion (η * α ^ J) (β u)) ∧
        t - s ≤ 16 * exitTailLength η α J ∧
        (∀ u ∈ Icc s t, |β u 1| + |β u 3| ≤ A * b / 2 ∧
          |coreRadius (β u 0) (β u 2) - coreRadius (β s 0) (β s 2)| ≤ 40 * A * b ∧
          2 + α < coreRadius (β u 0) (β u 2) ∧ |β u 1| ≤ β u 2 / 2) := by
  obtain ⟨A, hA, ε₀, hε₀, HP⟩ := exists_normalized_exit_prefix_bounds ⟨hη.1, hη.2.le⟩ hJ
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min ε₀ (1 / (1000 * A))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨A, hA, ε, hε, ?_⟩
  intro x t₀ s α b hc hs hα hb hsmall hAinit β hM hV hR hw
  let h := η * α ^ J
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.1.le
    dsimp only [h]
    nlinarith only [H, hη.2]
  have hbε : b ≤ ε := hsmall.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hε.le)
  have hAb : A * b ≤ 1 / 1000 := by
    have H := (le_div_iff₀ (by positivity : 0 < 1000 * A)).mp (hbε.trans (min_le_right _ _))
    nlinarith only [H]
  have hbsmall : b ≤ ε₀ * α ^ J :=
    hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have hprefix (t : ℝ) (hst : s ≤ t)
      (hAf : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
      (hreg : ∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) :=
    HP x t₀ s t α b hc hs hst hα hb hbsmall hAf hreg hV hR hw
  have hRstrict : 7 / 4 < coreRadius (β s 0) (β s 2) ∧ coreRadius (β s 0) (β s 2) < 17 / 4 := by
    rw [hR]
    constructor <;> linarith only [hα.1, hα.2]
  have hbs : b ≤ 1 / 1000 := by nlinarith only [hA, hb, hAb]
  have hus : |β s 1| < 1 / 100 := by linarith only [hw, hbs, abs_nonneg (β s 3)]
  have hws : |β s 3| < 1 / 100 := by linarith only [hw, hbs, abs_nonneg (β s 1)]
  have hvs : h < β s 2 ∧ β s 2 ≤ 1 := by rw [hV]; exact ⟨hh1, le_rfl⟩
  obtain ⟨r₀, hr₀, hlocal⟩ := normalized_exit_local_prefix hc hh hs hAinit hM hRstrict hus hvs hws
  let S : Set ℝ := {u | 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ exitPhysicalRegion h (β u)}
  have hsS : s ∈ S := ⟨(hlocal s ⟨le_rfl, hr₀.le⟩).1.le, (hlocal s ⟨le_rfl, hr₀.le⟩).2⟩
  have hex : ∃ t > s, β t 2 = h ∧ ∀ u ∈ Icc s t, u ∈ S := by
    by_contra hnone
    let T := s + 16 * exitTailLength η α J + 1
    have hL := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
    have hsT : s ≤ T := by dsimp only [T]; linarith only [hL]
    have hwhole : Icc s T ⊆ S := by
      apply (isClosed_normalized_exit_times hc hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
      intro t ht hbefore
      have htS := hbefore ⟨ht.1, le_rfl⟩
      have hAf (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
        lt_of_lt_of_le (by norm_num) (hbefore hu).1
      have H := hprefix t ht.1 hAf (fun u hu => (hbefore hu).2)
      have hu : |β t 1| < 1 / 100 := by linarith only [H.1, hAb, abs_nonneg (β t 3)]
      have hw' : |β t 3| < 1 / 100 := by linarith only [H.1, hAb, abs_nonneg (β t 1)]
      have hRt : 7 / 4 < coreRadius (β t 0) (β t 2) ∧ coreRadius (β t 0) (β t 2) < 17 / 4 := by
        have Hr := H.2.1
        rw [hR] at Hr
        constructor
        · linarith only [H.2.2.1, hα.1]
        · linarith only [(abs_le.mp Hr).2, hα.2, hAb]
      have hvlt : h < β t 2 := by
        rcases eq_or_lt_of_le ht.1 with heq | hst
        · subst t
          exact hvs.1
        · apply lt_of_le_of_ne htS.2.2.2.2.1.1
          intro heq
          exact hnone ⟨t, hst, heq.symm, fun u hu => hbefore hu⟩
      obtain ⟨r, htr, hafter⟩ := normalized_exit_local_prefix hc hh (hs.trans ht.1) (hAf t ⟨ht.1, le_rfl⟩)
        (exitPhysicalRegion_phase_bounds hh htS.2).2 hRt hu ⟨hvlt, htS.2.2.2.2.1.2⟩ hw'
      apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
      exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
    have H := (normalized_exit_residence hc hh hs hsT
      (fun u hu => lt_of_lt_of_le (by norm_num) (hwhole hu).1) (fun u hu => (hwhole hu).2) hV).2
    have hlog : Real.log (1 / h) = exitTailLength η α J := by
      rw [one_div, Real.log_inv]
      change -Real.log (η * α ^ J) = _
      rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
    rw [hlog] at H
    dsimp only [T] at H
    linarith only [H]
  obtain ⟨t, hst, hhit, hwhole⟩ := hex
  have hAf (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by norm_num) (hwhole u hu).1
  refine ⟨t, hst, hhit, hwhole, ?_, ?_⟩
  · have H := (normalized_exit_residence hc hh hs hst.le hAf (fun u hu => (hwhole u hu).2) hV).2
    have he : Real.log (1 / h) = exitTailLength η α J := by
      rw [one_div, Real.log_inv]
      change -Real.log (η * α ^ J) = _
      rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
    rwa [he] at H
  · intro u hu
    exact hprefix u hu.1 (fun q hq => hAf q ⟨hq.1, hq.2.trans hu.2⟩)
      (fun q hq => (hwhole q ⟨hq.1, hq.2.trans hu.2⟩).2)
