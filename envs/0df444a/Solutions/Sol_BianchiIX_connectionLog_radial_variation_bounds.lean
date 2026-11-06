-- Prove2me | solution 1 for BianchiIX.connectionLog_radial_variation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:00:18.014451+00:00
-- url     : https://prove2.me/submissions/e9b96c11-db25-4e3f-b20b-4b3680f8f947

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Analysis_ConnectionTransverseCoefficients
import Definitions.Def_BianchiIX_Dynamics_ConnectionTransverseDissipation
import Definitions.Def_BianchiIX_Analysis_ConnectionLogLinearization
import Definitions.Def_BianchiIX_Analysis_ConnectionWeightedVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
import Definitions.Def_BianchiIX_Analysis_ConnectionForcingBounds
import Theorems.Thm_BianchiIX_abs_bounds_of_forced_derivative_feedback
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionPhaseGPartials_bounds
import Theorems.Thm_BianchiIX_connectionStrongClockPartials_bounds
import Theorems.Thm_BianchiIX_connectionWeakClockPartials_bounds
import Theorems.Thm_BianchiIX_connection_weak_clock_rates
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem BianchiIX.signedRowSum_sub_scalar {A : Matrix ι ι ℝ} (c : ℝ) (i : ι) :
    signedRowSum (A - c • (1 : Matrix ι ι ℝ)) i = signedRowSum A i - c := by
  have H : (∑ j ∈ Finset.univ.erase i, |(A - c • (1 : Matrix ι ι ℝ)) i j|) =
      ∑ j ∈ Finset.univ.erase i, |A i j| := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [Matrix.sub_apply, Matrix.smul_apply, hij]
  unfold signedRowSum
  rw [H]
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_slope_right_le_of_forced_signedRowSum {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} {q : ι → ℝ} (hf : HasDerivAt f (A.mulVec (f t) + q) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ + ‖q‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by
  let g : ℝ → (ι → ℝ) := fun s => f s - (s - t) • q
  have hgt : g t = f t := by simp [g]
  have hg : HasDerivAt g (A.mulVec (g t)) t := by
    rw [hgt]
    convert! hf.sub (((hasDerivAt_id t).sub_const t).smul_const q) using 1
    simp
  have H := norm_slope_right_le_of_signedRowSum hg hA
    (r := r - ‖q‖) (by rw [hgt]; linarith only [hr])
  filter_upwards [H, self_mem_nhdsWithin] with s hs hst
  have hh : 0 < s - t := sub_pos.mpr hst
  have hnorm : ‖f s‖ - ‖g s‖ ≤ (s - t) * ‖q‖ := by
    have H' := norm_sub_norm_le (f s) (g s)
    have heq : f s - g s = (s - t) • q := by dsimp [g]; abel
    rwa [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at H'
  have H' := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * ‖q‖) = ‖q‖ := by field_simp
  rw [hid] at H'
  rw [hgt] at hs
  nlinarith only [hs, H']

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_of_forced_signedRowSum_nonpos {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀ t ∈ Ico a b, HasDerivAt B (B' t) t)
    (hinit : ‖f a‖ ≤ B a) (hq : ∀ t ∈ Ico a b, ‖q t‖ ≤ B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hf) hinit hB (fun t ht => (hB' t ht).hasDerivWithinAt)
  intro t ht r hr
  have H := norm_slope_right_le_of_forced_signedRowSum (hderiv t ht) (hA t ht)
    (r := r) (by simpa only [zero_mul, zero_add] using (hq t ht).trans_lt hr)
  simpa only [slope_def_module, smul_eq_mul, Function.comp_apply] using H.frequently

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_moments_le_of_linear_dissipation {f f' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hdecay : ∀ t ∈ Icc a b, f' t ≤ -c * f t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t) ≤ f a / c ∧ (∫ t in a..b, (t - a) * f t) ≤ f a / c ^ 2 := by
  have hcont := HasDerivAt.continuousOn hf
  refine ⟨integral_le_of_dissipation hab hc hf hcont hdecay hfb, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (1 + c * (s - a)) * f s)
        (c * f t + (1 + c * (t - a)) * f' t) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul c).const_add 1).mul (hf t ht) using 1
    simp
  have H := integral_le_of_dissipation (g := fun t => (t - a) * f t) hab (sq_pos_of_pos hc) hd
    ((continuousOn_id.sub continuousOn_const).mul hcont) (fun t ht => ?_) ?_
  · simpa only [sub_self, mul_zero, add_zero, one_mul] using H
  · have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hfactor : 0 ≤ 1 + c * (t - a) := by positivity
    have H' := mul_le_mul_of_nonneg_left (hdecay t ht) hfactor
    nlinarith only [H']
  · exact mul_nonneg (by positivity) hfb

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_exp_of_forced_budget {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {E E' B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (E' t) t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ -E' t)
    (hEa : ∀ t ∈ Icc a b, E t ≤ E a)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hinit : ‖f a‖ ≤ B a) (hq : ∀ t ∈ Icc a b, ‖q t‖ ≤ B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (E a - E t) * B t := by
  let g : ℝ → (ι → ℝ) := fun t => Real.exp (E t) • f t
  let M : ℝ → Matrix ι ι ℝ := fun t => A t - (-E' t) • (1 : Matrix ι ι ℝ)
  let c : ℝ → (ι → ℝ) := fun t => Real.exp (E t) • q t
  have hg (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g ((M t).mulVec (g t) + c t) t := by
    convert! (hE t ht).exp.smul (hf t ht) using 1
    dsimp [M, g, c]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hM (t : ℝ) (ht : t ∈ Ico a b) (i : ι) : signedRowSum (M t) i ≤ 0 := by
    dsimp [M]
    rw [signedRowSum_sub_scalar]
    exact sub_nonpos.mpr (hA t (Ico_subset_Icc_self ht) i)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : ‖c t‖ ≤ Real.exp (E a) * B' t := by
    simp only [c, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hq t ht) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hEa t ht))
        ((norm_nonneg _).trans (hq t ht)))
  have H := norm_le_of_forced_signedRowSum_nonpos (HasDerivAt.continuousOn hg)
    (fun t ht => hg t (Ico_subset_Icc_self ht)) hM
    (HasDerivAt.continuousOn (fun t ht => (hB t ht).const_mul (Real.exp (E a))))
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).const_mul (Real.exp (E a)))
    (by simpa only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left hinit (Real.exp_pos (E a)).le)
    (fun t ht => hbound t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at H'
  calc
    ‖f t‖ = Real.exp (-E t) * (Real.exp (E t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-E t) * (Real.exp (E a) * B t) :=
      mul_le_mul_of_nonneg_left H' (Real.exp_pos _).le
    _ = Real.exp (E a - E t) * B t := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_integral_envelope_of_forced_budget {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {E E' R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (E' t) t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ -E' t)
    (hEa : ∀ t ∈ Icc a b, E t ≤ E a) (hR : ContinuousOn R (Icc a b))
    (hq : ∀ t ∈ Icc a b, ‖q t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (E a - E b) * (‖f a‖ + ∫ t in a..b, R t) := by
  let r : ℝ → ℝ := fun t => R (projIcc a b hab t)
  have hr : Continuous r := hR.domRestrict.comp continuous_projIcc
  have hre (t : ℝ) (ht : t ∈ Icc a b) : r t = R t := by
    simp only [r, projIcc_of_mem hab ht]
  have hB (t : ℝ) : HasDerivAt (fun s => ‖f a‖ + ∫ u in a..s, r u) (r t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable _ _)
      hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt).const_add _
  have H := norm_le_exp_of_forced_budget hf hE hA hEa (fun t _ => hB t)
    (by simp) (fun t ht => by rw [hre t ht]; exact hq t ht) b ⟨hab, le_rfl⟩
  have heq : (∫ t in a..b, r t) = ∫ t in a..b, R t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hre t (uIcc_of_le hab ▸ ht)
  rwa [heq] at H

end
end

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

private theorem BianchiIX.connection_strong_clock_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤ -μ / 2 := by
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hDpos : 0 < connectionSpeed m u v w := by linarith only [hD, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hprod := mul_nonneg (show 0 ≤ m - μ + 1 / 2 by linarith only [(abs_le.mp hm).1]) hm0
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  apply (div_le_iff₀ hDpos).mpr
  dsimp [connectionStrongRate, connectionSpeed]
  nlinarith only [hprod, hu2, (abs_le.mp hm).2, hμ, sq_nonneg (v - w),
    mul_nonneg (show 0 ≤ μ by linarith only [hμ]) hc]

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
open Set MeasureTheory

private theorem BianchiIX.abs_bounds_of_derivative_feedback {f f' k : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hbudget : (∫ t in a..b, k t) ≤ Λ) (hΛ : Λ < 1)
    (hfeedback : ∀ Q : ℝ, 0 ≤ Q → (∀ t ∈ Icc a b, |f t| ≤ Q) →
      ∀ t ∈ Icc a b, |f' t| ≤ k t * Q) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| / (1 - Λ) ∧
      |f t - f a| ≤ Λ * |f a| / (1 - Λ) := by
  have H := abs_bounds_of_forced_derivative_feedback (e := fun _ => 0) hab hf hk hk0
    continuousOn_const (fun _ _ => le_rfl) hbudget hΛ
    (fun Q hQ hbound t ht => by simpa only [zero_add] using hfeedback Q hQ hbound t ht)
  simpa only [intervalIntegral.integral_zero, add_zero, zero_add] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_dissipative_moments {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) :
    (∫ z in a..b, Y z 1) ≤ 2 * Y a 1 / μ ∧
      (∫ z in a..b, (z - a) * Y z 1) ≤ 4 * Y a 1 / μ ^ 2 ∧
      (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) ≤ μ * (Y a 2 * Y a 3) ^ 2 / 4 ∧
      (∫ z in a..b, (z - a) * (Y z 2 * Y z 3) ^ 2) ≤ μ ^ 2 * (Y a 2 * Y a 3) ^ 2 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hD (z : ℝ) (hz : z ∈ Icc a b) : 0 < connectionClockRate (Y z) := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz)).1
    change μ / 2 ≤ connectionClockRate (Y z) at H
    linarith only [H, hμ]
  have hU (z : ℝ) (hz : z ∈ Icc a b) : connectionLogField (Y z) 1 ≤ -(μ / 2) * Y z 1 := by
    rw [(connectionLogField_components (ne_of_gt (hD z hz))).2.1]
    simpa only [neg_div, connectionClockRate, connectionSpeed] using mul_le_mul_of_nonneg_right
      (connection_strong_clock_rate_le hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)) (hu z hz).1
  have HU := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < μ / 2)
    (fun z hz => hasDerivAt_pi.mp (hY z hz) 1) hU (hu b ⟨hab, le_rfl⟩).1
  have HP := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < 4 / μ)
    (fun z hz => (hasDerivAt_connectionLog_product (hY z hz) (ne_of_gt (hD z hz))).pow 2)
    (fun z hz => ?_) (sq_nonneg (Y b 2 * Y b 3))
  · refine ⟨HU.1.trans_eq (by ring), HU.2.trans_eq (by ring), HP.1.trans_eq ?_, HP.2.trans_eq ?_⟩
    · simp only [Pi.pow_apply]
      field_simp
    · simp only [Pi.pow_apply]
      field_simp
      norm_num
  · have H := mul_le_mul_of_nonneg_right
      (connection_weak_clock_rates hμ (hm z hz) (hu z hz) (hv' z hz) (hw z hz) (huv z hz)).2
      (by positivity : 0 ≤ 2 * (Y z 2 * Y z 3) ^ 2)
    simp only [Pi.pow_apply, connectionClockRate]
    convert! H using 1 <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionTransverseMatrix_rows {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (i : Fin 2) :
    (∑ j : Fin 2, |connectionTransverseMatrix μ m u v w i j|) ≤
      connectionTransverseRate μ u v w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hu0 := hu.1
  have hv0 := hv.1
  have hw0 := hw.1
  have huv : u * v ≤ u := by nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu0]
  have hinv : 1 / μ ≤ 1 := (div_le_one hμ0).mpr (by linarith only [hμ])
  have hinv2 : 1 / μ ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hμ0)).mpr hμ2
  have ha := connectionStrongClockPartials_bounds hμ hm hu hv hw
  have hb := connectionWeakClockPartials_bounds hμ hm hu hv hw
  have hdiv (r : ℝ) : |r / μ ^ 2| = |r| / μ ^ 2 := by rw [abs_div, abs_of_pos (sq_pos_of_pos hμ0)]
  rw [Fin.sum_univ_two]
  fin_cases i
  · change |connectionStrongClockPartials m u v w 1| +
      |connectionStrongClockPartials m u v w 2 / μ ^ 2| ≤ connectionTransverseRate μ u v w
    rw [hdiv]
    have H := add_le_add ha.2.1 (div_le_div_of_nonneg_right ha.2.2.1 (sq_nonneg μ))
    have huv' : u * v / μ ^ 2 ≤ u :=
      (div_le_div_of_nonneg_right huv (sq_nonneg μ)).trans
        (by simpa only [one_div, div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hinv2 hu0)
    have hmain : 32 * u + 32 * ((v ^ 2 + v * w) / μ + u * v) / μ ^ 2 =
        32 * (u + v ^ 2 / μ ^ 3 + v * w / μ ^ 3 + u * v / μ ^ 2) := by ring
    rw [hmain] at H
    dsimp [connectionTransverseRate]
    have hv2 : 0 ≤ v ^ 2 / μ ^ 3 := by positivity
    have hp : 0 ≤ v * w / μ ^ 3 := by positivity
    nlinarith only [H, huv', hv2, hp, hu0, mul_nonneg (sub_nonneg.mpr hμ) hu0]
  · change |μ ^ 2 * connectionWeakClockPartials m u v w 1| +
      |connectionWeakClockPartials m u v w 2| ≤ connectionTransverseRate μ u v w
    rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
    have H := add_le_add (mul_le_mul_of_nonneg_left hb.2.1 (sq_nonneg μ)) hb.2.2.1
    have hid : μ ^ 2 * (64 * u / μ) = 64 * μ * u := by field_simp
    rw [hid] at H
    have huv' : u * v / μ ≤ u :=
      (div_le_div_of_nonneg_right huv hμ0.le).trans
        (by simpa only [one_div, div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hinv hu0)
    dsimp [connectionTransverseRate]
    have hp : 0 ≤ v * w / μ ^ 3 := by positivity
    nlinarith only [H, huv', hp, mul_nonneg (show 0 ≤ μ - 1 by linarith only [hμ]) hu0]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionTransverseMatrix_signedRows {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (i : Fin 2) :
    signedRowSum (connectionTransverseMatrix μ m u v w) i ≤ connectionTransverseRate μ u v w := by
  apply le_trans _ (connectionTransverseMatrix_rows hμ hm hu hv hw i)
  have hfin : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  fin_cases i
  · simpa [signedRowSum, hfin] using le_abs_self (connectionTransverseMatrix μ m u v w 0 0)
  · simpa [signedRowSum, hfin, add_comm] using
      add_le_add_right (le_abs_self (connectionTransverseMatrix μ m u v w 1 1))
        |connectionTransverseMatrix μ m u v w 1 0|

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionTransverseBudget_nonneg {μ u v w : ℝ} (hμ : 0 ≤ μ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ connectionTransverseBudget μ u v w := by
  unfold connectionTransverseBudget
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionTransverseBudget_entry {μ u v w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) : connectionTransverseBudget μ u v w ≤ 2533 / 5000 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu' : u ≤ 1 / 40000 := by
    calc
      u ≤ (1 / 10000) / μ := hu.2
      _ ≤ (1 / 10000) / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hμ
      _ = _ := by norm_num
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2, mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hp : v * w ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hv.2 hw.1).trans (by simpa using hw.2)
  have H1 : v ^ 2 / (2 * μ ^ 3) ≤ 1 / 128 := by
    calc
      _ ≤ 1 / (2 * μ ^ 3) := div_le_div_of_nonneg_right hv2 (by positivity)
      _ ≤ 1 / 128 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hμ3])
  have H2 : v * w / (2 * μ ^ 2) ≤ 1 / 320000 := by
    calc
      _ ≤ (1 / 10000) / (2 * μ ^ 2) := div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ (1 / 10000) / 32 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hμ2])
      _ = _ := by norm_num
  unfold connectionTransverseBudget
  linarith only [hu', H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exp_connectionTransverseBudget_lt_two {μ u v w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) : Real.exp (connectionTransverseBudget μ u v w) < 2 := by
  have H := connectionTransverseBudget_entry hμ hu hv hw
  have H' := Real.exp_lt_two_add_div_two_sub (x := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  have hE : connectionTransverseBudget μ u v w ≤ 2 / 3 := H.trans (by norm_num)
  exact (Real.exp_le_exp.mpr hE).trans_lt (by norm_num at H'; exact H')

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionTransverseBudget {Y : ℝ → ProjectiveState} {μ t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) :
    HasDerivAt (fun s => connectionTransverseBudget μ (Y s 1) (Y s 2) (Y s 3))
      (connectionTransverseBudgetDerivative μ (Y t)) t := by
  have hu := hasDerivAt_pi.mp hY 1
  have hv := hasDerivAt_pi.mp hY 2
  have hw := hasDerivAt_pi.mp hY 3
  convert! (((hu.const_mul 4).add ((hv.pow 2).div_const (2 * μ ^ 3))).add
    ((hv.mul hw).div_const (2 * μ ^ 2))).const_mul 64 using 1
  simp only [connectionTransverseBudgetDerivative, Nat.cast_ofNat, Nat.reduceSub, pow_one]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionTransverseBudget_dissipation {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (huv : y 1 ≤ y 2) :
    connectionTransverseBudgetDerivative μ y ≤ -connectionTransverseRate μ (y 1) (y 2) (y 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hv0 := hv.1
  have hD : 0 < connectionClockRate y := by
    have H := (connection_speed_bounds hμ hm hu hv hw).1
    change μ / 2 ≤ connectionClockRate y at H
    linarith only [H, hμ]
  have hfield := connectionLogField_components (ne_of_gt hD)
  have hU : connectionLogField y 1 ≤ -μ / 2 * y 1 := by
    rw [hfield.2.1]
    exact mul_le_mul_of_nonneg_right (connection_strong_clock_rate_le hμ hm hu hv hw huv) hu.1
  have hweak := connection_weak_clock_rates hμ hm hu hv hw huv
  have hV : connectionLogField y 2 ≤ -y 2 := by
    rw [hfield.2.2.1]
    have H := mul_le_mul_of_nonneg_right hweak.1 hv.1
    simp only [neg_neg] at H
    have H' : 0 ≤ (2 / μ) * y 2 := mul_nonneg (by positivity) hv.1
    change (y 0 - 1 - coupling (y 1) (y 2) (y 3)) / connectionClockRate y * y 2 ≤ _ at H
    linarith only [H, H']
  have hP : connectionLogField y 2 * y 3 + y 2 * connectionLogField y 3 ≤
      -2 / μ * (y 2 * y 3) := by
    have hid : connectionLogField y 2 * y 3 + y 2 * connectionLogField y 3 =
        (-2 * (1 + coupling (y 1) (y 2) (y 3)) / connectionClockRate y) * (y 2 * y 3) := by
      rw [hfield.2.2.1, hfield.2.2.2]
      dsimp [connectionClockRate, connectionSpeed] at *
      field_simp
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hweak.2 (mul_nonneg hv.1 hw.1)
  have H := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 4))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2 * y 2))
      (by positivity : 0 ≤ 2 * μ ^ 3)))
    (div_le_div_of_nonneg_right hP (by positivity : 0 ≤ 2 * μ ^ 2))
  apply (mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ) ≤ 64)).trans_eq
  dsimp [connectionTransverseRate]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionLog_transverse_budget_antitone {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hμ : 4 ≤ μ) (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (huv : ∀ z ∈ Icc a b, Y z 1 ≤ Y z 2) :
    AntitoneOn (fun z => connectionTransverseBudget μ (Y z 1) (Y z 2) (Y z 3)) (Icc a b) := by
  have hd (z : ℝ) (hz : z ∈ Icc a b) := hasDerivAt_connectionTransverseBudget (μ := μ) (hY z hz)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hd z (interior_subset hz)).deriv]
  apply (connectionTransverseBudget_dissipation hμ (hm z (interior_subset hz))
    (hu z (interior_subset hz)) (hv z (interior_subset hz)) (hw z (interior_subset hz))
    (huv z (interior_subset hz))).trans
  have hμ0 : 0 ≤ μ := by linarith only [hμ]
  have hu0 := (hu z (interior_subset hz)).1
  have hv0 := (hv z (interior_subset hz)).1
  have hw0 := (hw z (interior_subset hz)).1
  apply neg_nonpos.mpr
  dsimp [connectionTransverseRate]
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionWeightedTangent_linearized {μ : ℝ} (hμ : μ ≠ 0) (y : ProjectiveState) (d : Fin 4 → ℝ) :
    connectionWeightedTangent μ (connectionLogLinearizedRates y d) =
      (connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec (connectionWeightedTangent μ d) +
        d 0 • connectionPhaseColumn μ y + d 3 • connectionWallColumn μ y := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let a := connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3)
  let b := connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3)
  fin_cases i
  · change (∑ j : Fin 4, a j * d j) = a 1 * d 1 + a 2 / μ ^ 2 * (μ ^ 2 * d 2) + d 0 * a 0 + d 3 * a 3
    simp [Fin.sum_univ_succ]
    field_simp
    ring
  · change μ ^ 2 * (∑ j : Fin 4, b j * d j) =
      (μ ^ 2 * b 1) * d 1 + b 2 * (μ ^ 2 * d 2) + d 0 * (μ ^ 2 * b 0) + d 3 * (μ ^ 2 * b 3)
    simp [Fin.sum_univ_succ]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionWeightedTangent {D : ℝ → (Fin 4 → ℝ)} {Y : ℝ → ProjectiveState} {μ t : ℝ}
    (hμ : μ ≠ 0) (hD : HasDerivAt D (connectionLogLinearizedRates (Y t) (D t)) t) :
    HasDerivAt (fun s => connectionWeightedTangent μ (D s))
      ((connectionTransverseMatrix μ (-Y t 0) (Y t 1) (Y t 2) (Y t 3)).mulVec (connectionWeightedTangent μ (D t)) +
        D t 0 • connectionPhaseColumn μ (Y t) + D t 3 • connectionWallColumn μ (Y t)) t := by
  rw [← connectionWeightedTangent_linearized hμ]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hD 1
  · exact (hasDerivAt_pi.mp hD 2).const_mul (μ ^ 2)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseColumn_norm {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    ‖connectionPhaseColumn μ y‖ ≤ 64 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 0‖ ≤ 64
    rw [Real.norm_eq_abs]
    exact (connectionStrongClockPartials_bounds hμ hm hu hv hw).1.trans (by norm_num)
  · change ‖μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 0‖ ≤ 64
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).1 (sq_nonneg μ)).trans_eq
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseColumn_forcing {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (Z : ℝ) :
    ‖Z • connectionPhaseColumn μ y‖ ≤ 64 * |Z| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (connectionPhaseColumn_norm hμ hm hu hv hw) (abs_nonneg Z)).trans_eq (mul_comm _ _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackRate_nonneg {μ τ u p : ℝ} (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackRate μ τ u p := by
  unfold connectionPhaseFeedbackRate
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackBudget_nonneg {μ u p : ℝ} (hμ : 0 ≤ μ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackBudget μ u p := by
  unfold connectionPhaseFeedbackBudget
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackBudget_small {μ u p : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hp : 0 ≤ p ∧ p ≤ 1 / 10000) :
    connectionPhaseFeedbackBudget μ u p ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hp2 : p ^ 2 ≤ 1 / 100000000 := by nlinarith only [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
  have H1 : u / μ ^ 3 ≤ 1 / 2560000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have H2 : u / μ ^ 2 ≤ 1 / 640000 :=
    (div_le_div_of_nonneg_right hu' (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (0 : ℝ) < 16) hμ2).trans_eq (by norm_num))
  have H3 : p ^ 2 / μ ^ 3 ≤ 1 / 6400000000 :=
    (div_le_div_of_nonneg_right hp2 (by positivity)).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 100000000) (by norm_num : (0 : ℝ) < 64) hμ3).trans_eq (by norm_num))
  have hid : connectionPhaseFeedbackBudget μ u p = 128 * (u / μ ^ 3) +
      32768 * (u / μ ^ 2) + 528 * (p ^ 2 / μ ^ 3) := by unfold connectionPhaseFeedbackBudget; ring
  rw [hid]
  linarith only [H1, H2, H3]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhase_transverse_row_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 1| +
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 2| / μ ^ 2 ≤
        64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have huv : y 1 * y 2 / μ ^ 2 ≤ y 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hμ0)).mpr
    exact (mul_le_mul_of_nonneg_left hv.2 hu.1).trans
      (by simpa using mul_le_mul_of_nonneg_left hμ2 hu.1)
  have H := add_le_add hG.2.1 (div_le_div_of_nonneg_right hG.2.2.1 (sq_nonneg μ))
  have hid : 32 * (y 1 * y 2 + (y 2 * y 3) ^ 2 / μ ^ 3) / μ ^ 2 =
      32 * (y 1 * y 2 / μ ^ 2) + 32 * ((y 2 * y 3) ^ 2 / μ ^ 5) := by field_simp
  rw [hid] at H
  have hp : 0 ≤ (y 2 * y 3) ^ 2 / μ ^ 5 := by positivity
  linarith only [H, huv, hp]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhase_variation_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (d : Fin 4 → ℝ) (hz : d 3 = 0) :
    |connectionLogLinearizedRates y d 0| ≤
      64 * (y 1 / μ ^ 2 + (y 2 * y 3) ^ 2 / μ ^ 4) * |d 0| +
      64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * ‖connectionWeightedTangent μ d‖ := by
  let G := connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hx : |d 1| ≤ ‖connectionWeightedTangent μ d‖ := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs] using norm_le_pi_norm (connectionWeightedTangent μ d) 0
  have hy : |d 2| ≤ ‖connectionWeightedTangent μ d‖ / μ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hμ0)).mpr
    have H := norm_le_pi_norm (connectionWeightedTangent μ d) 1
    simpa [connectionWeightedTangent, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ), mul_comm] using H
  have hsum : |connectionLogLinearizedRates y d 0| ≤ |G 0| * |d 0| + |G 1| * |d 1| + |G 2| * |d 2| := by
    change |∑ j : Fin 4, G j * d j| ≤ _
    simpa [Fin.sum_univ_succ, abs_mul, hz, add_assoc] using
      (abs_add_le (G 0 * d 0) (G 1 * d 1 + G 2 * d 2)).trans
        (add_le_add (le_refl |G 0 * d 0|) (abs_add_le (G 1 * d 1) (G 2 * d 2)))
  have H := hsum.trans (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left hy (abs_nonneg _)))
  have hJ := (connectionPhaseGPartials_bounds hμ hm hu hv hw).1
  have hT := connectionPhase_transverse_row_bound hμ hm hu hv hw
  calc
    _ ≤ |G 0| * |d 0| + (|G 1| + |G 2| / μ ^ 2) * ‖connectionWeightedTangent μ d‖ := H.trans_eq (by ring)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hJ (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_connectionWallForcingEnvelope (μ : ℝ) :
    Continuous (connectionWallForcingEnvelope μ) := by
  unfold connectionWallForcingEnvelope
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionWallColumn_norm {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    ‖connectionWallColumn μ y‖ ≤ connectionWallForcingEnvelope μ y := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have huw : 0 ≤ y 1 * y 3 := mul_nonneg hu.1 hw.1
  have hvw : 0 ≤ y 2 * y 3 / μ := div_nonneg (mul_nonneg hv.1 hw.1) hμ0.le
  have hbase : 0 ≤ (y 3 ^ 2 + y 2 * y 3) / μ :=
    div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hv.1 hw.1)) hμ0.le
  have hmul : y 1 * y 3 ≤ μ * y 1 * y 3 := by nlinarith only [hμ, huw]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3‖ ≤ _
    rw [Real.norm_eq_abs]
    apply (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.2.2.trans
    dsimp [connectionWallForcingEnvelope]
    nlinarith only [hbase, huw, hmul]
  · change ‖μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.2.2
      (sq_nonneg μ)).trans
    have hid : μ ^ 2 * (64 * (y 3 ^ 2 / μ ^ 3 + y 1 * y 3 / μ)) =
        64 * (y 3 ^ 2 / μ + μ * y 1 * y 3) := by field_simp
    rw [hid]
    dsimp [connectionWallForcingEnvelope]
    rw [add_div]
    linarith only [hvw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionWeighted_forcing_bound {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (Z ζ : ℝ) :
    ‖Z • connectionPhaseColumn μ y + ζ • connectionWallColumn μ y‖ ≤
      64 * |Z| + |ζ| * connectionWallForcingEnvelope μ y := by
  apply (norm_add_le _ _).trans
  apply add_le_add (connectionPhaseColumn_forcing hμ hm hu hv hw Z)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (connectionWallColumn_norm hμ hm hu hv hw) (abs_nonneg ζ)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_transverse_forced_exp {Y : ℝ → ProjectiveState} {ξ q : ℝ → (Fin 2 → ℝ)}
    {R : ℝ → ℝ} {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (huv : ∀ z ∈ Icc a b, Y z 1 ≤ Y z 2)
    (hξ : ∀ z ∈ Icc a b, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) + q z) z)
    (hR : ContinuousOn R (Icc a b)) (hq : ∀ z ∈ Icc a b, ‖q z‖ ≤ R z) :
    ‖ξ b‖ ≤ Real.exp (connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) -
      connectionTransverseBudget μ (Y b 1) (Y b 2) (Y b 3)) * (‖ξ a‖ + ∫ z in a..b, R z) := by
  have hanti := connectionLog_transverse_budget_antitone hμ hY hm hu hv hw huv
  apply norm_le_integral_envelope_of_forced_budget hab hξ
    (fun z hz => hasDerivAt_connectionTransverseBudget (μ := μ) (hY z hz))
    (fun z hz i => ?_) (fun z hz => hanti ⟨le_rfl, hab⟩ hz hz.1) hR hq
  have Hr := connectionTransverseMatrix_signedRows hμ (hm z hz) (hu z hz) (hv z hz) (hw z hz) i
  have HE := connectionTransverseBudget_dissipation hμ (hm z hz) (hu z hz) (hv z hz) (hw z hz) (huv z hz)
  linarith only [Hr, HE]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_transverse_forced {Y : ℝ → ProjectiveState} {ξ q : ℝ → (Fin 2 → ℝ)}
    {R : ℝ → ℝ} {μ a b s t : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hξ : ∀ z ∈ Icc s t, HasDerivAt ξ
      ((connectionTransverseMatrix μ (-Y z 0) (Y z 1) (Y z 2) (Y z 3)).mulVec (ξ z) + q z) z)
    (hR : ContinuousOn R (Icc s t)) (hq : ∀ z ∈ Icc s t, ‖q z‖ ≤ R z) :
    ‖ξ t‖ ≤ 2 * (‖ξ s‖ + ∫ z in s..t, R z) := by
  have huv := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).1
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have H := connectionLog_transverse_forced_exp hst hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
    (fun z hz => hv' z (hsub hz)) (fun z hz => hw z (hsub hz)) (fun z hz => huv z (hsub hz)) hξ hR hq
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hanti := connectionLog_transverse_budget_antitone hμ hY hm hu hv' hw huv
  have hE : connectionTransverseBudget μ (Y s 1) (Y s 2) (Y s 3) -
      connectionTransverseBudget μ (Y t 1) (Y t 2) (Y t 3) ≤
      connectionTransverseBudget μ (Y a 1) (Y a 2) (Y a 3) :=
    (sub_le_self _ (connectionTransverseBudget_nonneg (by linarith only [hμ]) (hu t ht).1
      (hv t ht).1.le (hw t ht).1)).trans (hanti ha hs hs.1)
  have he := (Real.exp_le_exp.mpr hE).trans_lt
    (exp_connectionTransverseBudget_lt_two hμ ⟨(hu a ha).1, hsmall⟩ (hv' a ha) ⟨(hw a ha).1, hwall⟩)
  have hi : 0 ≤ ∫ z in s..t, R z := intervalIntegral.integral_nonneg hst
    (fun z hz => (norm_nonneg _).trans (hq z hz))
  exact H.trans (mul_le_mul_of_nonneg_right he.le (add_nonneg (norm_nonneg _) hi))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_connectionPhaseFeedbackRate {U P : ℝ → ℝ} {μ a b : ℝ} (hab : a ≤ b)
    (hU : ContinuousOn U (Icc a b)) (hP : ContinuousOn P (Icc a b)) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (U z) (P z)) =
      (64 / μ ^ 2) * (∫ z in a..b, U z) + (64 / μ ^ 4) * (∫ z in a..b, P z ^ 2) +
      8192 * (∫ z in a..b, (z - a) * U z) + (8192 / μ ^ 5) * ∫ z in a..b, (z - a) * P z ^ 2 := by
  have htime : ContinuousOn (fun z : ℝ => z - a) (Icc a b) := continuousOn_id.sub continuousOn_const
  have h1 := (hU.const_mul (64 / μ ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have h2 := ((hP.pow 2).const_mul (64 / μ ^ 4)).intervalIntegrable_of_Icc (μ := volume) hab
  have h3 := ((htime.mul hU).const_mul 8192).intervalIntegrable_of_Icc (μ := volume) hab
  have h4 := ((htime.mul (hP.pow 2)).const_mul (8192 / μ ^ 5)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Pi.pow_apply, Pi.mul_apply] at h2 h3 h4
  have heq (z : ℝ) : connectionPhaseFeedbackRate μ (z - a) (U z) (P z) =
      (64 / μ ^ 2) * U z + (64 / μ ^ 4) * P z ^ 2 + 8192 * ((z - a) * U z) +
        (8192 / μ ^ 5) * ((z - a) * P z ^ 2) := by unfold connectionPhaseFeedbackRate; ring
  simp_rw [heq]
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_feedback_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)) ≤
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ∧
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := HasDerivAt.continuousOn hY
  have hU := continuousOn_pi.mp hc 1
  have hP : ContinuousOn (fun z => Y z 2 * Y z 3) (Icc a b) :=
    (continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)
  have H := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  constructor
  · rw [integral_connectionPhaseFeedbackRate (μ := μ) hab hU hP]
    apply (add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left H.1 (by positivity : 0 ≤ 64 / μ ^ 2))
        (mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0 ≤ 64 / μ ^ 4)))
      (mul_le_mul_of_nonneg_left H.2.1 (by norm_num : (0 : ℝ) ≤ 8192)))
      (mul_le_mul_of_nonneg_left H.2.2.2 (by positivity : 0 ≤ 8192 / μ ^ 5))).trans_eq
    unfold connectionPhaseFeedbackBudget
    field_simp
    ring
  · have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    apply connectionPhaseFeedbackBudget_small hμ ⟨(hu a ha).1, hsmall⟩
    refine ⟨mul_nonneg (hv a ha).1.le (hw a ha).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (hv a ha).2 (hw a ha).1).trans (by simpa using hwall)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_weighted_variation_bound {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b t ζ : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = ζ) (ht : t ∈ Icc a b) :
    ‖connectionWeightedTangent μ (D t)‖ ≤ 2 * ‖connectionWeightedTangent μ (D a)‖ +
      128 * (∫ z in a..t, |D z 0|) + 2 * |ζ| * ∫ z in a..t, connectionWallForcingEnvelope μ (Y z) := by
  have hμne : μ ≠ 0 := by linarith only [hμ]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hdc := (HasDerivAt.continuousOn hD).mono hsub
  have hphase : ContinuousOn (fun z => 64 * |D z 0|) (Icc a t) :=
    (continuousOn_pi.mp hdc 0).abs.const_mul 64
  have henv : ContinuousOn (fun z => |ζ| * connectionWallForcingEnvelope μ (Y z)) (Icc a t) :=
    ((continuous_connectionWallForcingEnvelope μ).comp_continuousOn
      ((HasDerivAt.continuousOn hY).mono hsub)).const_mul |ζ|
  have hder (z : ℝ) (hz : z ∈ Icc a t) := hasDerivAt_connectionWeightedTangent hμne (hD z (hsub hz))
  have H := connectionLog_transverse_forced hab hμ hY hm hu hv hw hentry hsmall hwall
    ⟨le_rfl, hab⟩ ht ht.1
    (fun z hz => by simpa only [hζ z (hsub hz), add_assoc] using hder z hz)
    (hphase.add henv) (fun z hz => connectionWeighted_forcing_bound hμ (hm z (hsub hz))
      (hu z (hsub hz)) ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz)) (D z 0) ζ)
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add (hphase.intervalIntegrable_of_Icc ht.1)
    (henv.intervalIntegrable_of_Icc ht.1), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  convert H using 1
  ring

end
end

/-- For a pure phase initial direction, feedback is absorbed without a running maximum or Gronwall. -/
theorem solution {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 0) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0) :
    ∀ t ∈ Icc a b, |D t 0| ≤ (16 / 15) * |D a 0| ∧
      |D t 0 - D a 0| ≤ (16 / 15) * connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) * |D a 0| ∧
      ‖connectionWeightedTangent μ (D t)‖ ≤ (2048 / 15) * (t - a) * |D a 0| := by
  let k : ℝ → ℝ := fun z => connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)
  let Λ := connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3)
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcoords (i : Fin 4) := continuousOn_pi.mp hcY i
  have hk : ContinuousOn k (Icc a b) := by
    dsimp [k, connectionPhaseFeedbackRate]
    fun_prop
  have hk0 (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ k z :=
    connectionPhaseFeedbackRate_nonneg hμ0.le (sub_nonneg.mpr hz.1) (hu z hz).1
  have hbudget := connectionLog_feedback_budget hab hμ hY hm hu hv hw hentry hsmall hwall
  have hΛ0 : 0 ≤ Λ := connectionPhaseFeedbackBudget_nonneg hμ0.le (hu a ⟨le_rfl, hab⟩).1
  have hΛ : Λ < 1 := hbudget.2.trans_lt (by norm_num)
  have hzero : connectionWeightedTangent μ (D a) = 0 := by simp [connectionWeightedTangent, hx0, hy0]
  have htrans (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z)‖ ≤ 128 * ∫ r in a..z, |D r 0| := by
    have H := connectionLog_weighted_variation_bound hab hμ hY hm hu hv hw hentry hsmall hwall hD hζ hz
    simpa only [hzero, norm_zero, mul_zero, zero_add, abs_zero, zero_mul, add_zero] using H
  have hcap (Q : ℝ) (hQ : ∀ z ∈ Icc a b, |D z 0| ≤ Q) (z : ℝ) (hz : z ∈ Icc a b) :
      ‖connectionWeightedTangent μ (D z)‖ ≤ 128 * (z - a) * Q := by
    have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc_right hz.2
    have HI := intervalIntegral.integral_mono_on (μ := volume) hz.1
      (((continuousOn_pi.mp hcD 0).abs.mono hsub).intervalIntegrable_of_Icc hz.1)
      (intervalIntegrable_const (c := Q)) (fun r hr => hQ r (hsub hr))
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    exact (htrans z hz).trans ((mul_le_mul_of_nonneg_left HI (by norm_num : (0 : ℝ) ≤ 128)).trans_eq (by ring))
  have H := abs_bounds_of_derivative_feedback (f := fun z => D z 0) (k := k) (Λ := Λ)
    hab (fun z hz => hasDerivAt_pi.mp (hD z hz) 0)
    hk hk0 hbudget.1 hΛ (fun Q _ hQ z hz => ?_)
  · have hfactor : 1 / (1 - Λ) ≤ 16 / 15 :=
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 15 / 16)
        (by linarith only [hbudget.2] : 15 / 16 ≤ 1 - Λ)).trans_eq (by norm_num)
    have hscale (c : ℝ) (hc : 0 ≤ c) : c / (1 - Λ) ≤ (16 / 15) * c := by
      calc
        _ = (1 / (1 - Λ)) * c := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hc
    have hfinal (z : ℝ) (hz : z ∈ Icc a b) : |D z 0| ≤ (16 / 15) * |D a 0| :=
      (H z hz).1.trans (hscale _ (abs_nonneg _))
    intro t ht
    refine ⟨hfinal t ht, ?_, ?_⟩
    · exact (H t ht).2.trans ((hscale _ (mul_nonneg hΛ0 (abs_nonneg (D a 0)))).trans_eq (by ring))
    · exact (hcap ((16 / 15) * |D a 0|) hfinal t ht).trans_eq (by ring)
  · have Hphase := connectionPhase_variation_bound hμ (hm z hz) (hu z hz)
      ⟨(hv z hz).1.le, (hv z hz).2⟩ (hw z hz) (D z) (hζ z hz)
    have hJ : 0 ≤ 64 * (Y z 1 / μ ^ 2 + (Y z 2 * Y z 3) ^ 2 / μ ^ 4) := by
      have hu0 := (hu z hz).1
      positivity
    have hT : 0 ≤ 64 * (Y z 1 + (Y z 2 * Y z 3) ^ 2 / μ ^ 5) := by
      have hu0 := (hu z hz).1
      positivity
    exact Hphase.trans ((add_le_add (mul_le_mul_of_nonneg_left (hQ z hz) hJ)
      (mul_le_mul_of_nonneg_left (hcap Q hQ z hz) hT)).trans_eq (by dsimp [k, connectionPhaseFeedbackRate]; ring))
