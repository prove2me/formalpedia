-- Prove2me | solution 1 for BianchiIX.connectionLog_growing_transverse_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:00:24.212513+00:00
-- url     : https://prove2.me/submissions/f3754f84-3169-4b1c-a2e0-3104d608915f

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Analysis_ConnectionTransverseCoefficients
import Definitions.Def_BianchiIX_Dynamics_ConnectionTransverseDissipation
import Definitions.Def_BianchiIX_Analysis_ConnectionLogLinearization
import Definitions.Def_BianchiIX_Analysis_ConnectionWeightedVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionGrowingSources
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_growing_moments
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc

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

private theorem BianchiIX.connectionTransverseMatrix_strong_forcing {μ : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) (x : ℝ) :
    ‖(connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec ![x, 0]‖ ≤
      64 * μ * y 1 * |x| := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · change ‖connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 1 * x + _ * 0‖ ≤ _
    rw [mul_zero, add_zero, Real.norm_eq_abs, abs_mul]
    apply (mul_le_mul_of_nonneg_right (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.1 (abs_nonneg x)).trans
    exact mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_right hμ hu.1, hu.1]) (abs_nonneg x)
  · change ‖(μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 1) * x + _ * 0‖ ≤ _
    rw [mul_zero, add_zero, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg μ)]
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.1 (sq_nonneg μ))
      (abs_nonneg x)).trans_eq
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_connectionGrowingSources (μ w : ℝ) :
    Continuous (connectionGrowingStrongSource μ w) ∧ Continuous (connectionGrowingWeakSource μ w) ∧
      Continuous (connectionGrowingPhaseSource μ w) := by
  unfold connectionGrowingStrongSource connectionGrowingWeakSource connectionGrowingPhaseSource
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionGrowingSources_nonneg {μ w : ℝ} {y : ProjectiveState}
    (hμ : 0 ≤ μ) (hw : 0 ≤ w) (hu : 0 ≤ y 1) (hv : 0 ≤ y 2) (hW : 0 ≤ y 3) :
    0 ≤ connectionGrowingStrongSource μ w y ∧ 0 ≤ connectionGrowingWeakSource μ w y ∧
      0 ≤ connectionGrowingPhaseSource μ w y := by
  unfold connectionGrowingStrongSource connectionGrowingWeakSource connectionGrowingPhaseSource
  exact ⟨by positivity, by positivity, by positivity⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionGrowingSources_bound {μ w : ℝ} {y : ProjectiveState} (hμ : 4 ≤ μ) (hw0 : 0 < w)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1) :
    |connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingStrongSource μ w y ∧
      |μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingWeakSource μ w y ∧
      |connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3) 3 / w| ≤ connectionGrowingPhaseSource μ w y := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  simp only [abs_div, abs_of_pos hw0]
  refine ⟨div_le_div_of_nonneg_right (connectionStrongClockPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le,
    ?_, div_le_div_of_nonneg_right (connectionPhaseGPartials_bounds hμ hm hu hv hw).2.2.2 hw0.le⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (connectionWeakClockPartials_bounds hμ hm hu hv hw).2.2.2 (sq_nonneg μ)) hw0.le).trans_eq
  unfold connectionGrowingWeakSource
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuousAt_connectionStrongWallColumn {Y : ℝ → ProjectiveState} {t : ℝ}
    (hc : ContinuousAt Y t) (hm : 1 < -Y t 0)
    (hD : connectionSpeed (-Y t 0) (Y t 1) (Y t 2) (Y t 3) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0) :
    ContinuousAt (fun s => connectionStrongClockPartials (-Y s 0) (Y s 1) (Y s 2) (Y s 3) 3) t := by
  have hcoord (i : Fin 4) : ContinuousAt (fun s => Y s i) t := (continuous_apply i).continuousAt.comp hc
  have hKp : phaseNorm (-Y t 0 + 1) (Y t 2) ≠ 0 := ne_of_gt (phaseNorm_pos (by linarith only [hm]))
  have hKm : phaseNorm (-Y t 0 - 1) (Y t 3) ≠ 0 := ne_of_gt (phaseNorm_pos (by linarith only [hm]))
  have hcKp : ContinuousAt (fun s => phaseNorm (-Y s 0 + 1) (Y s 2)) t := by unfold phaseNorm; fun_prop
  have hcKm : ContinuousAt (fun s => phaseNorm (-Y s 0 - 1) (Y s 3)) t := by unfold phaseNorm; fun_prop
  have hcf : ContinuousAt (fun s => matchingPhaseSlope (-Y s 0) (Y s 2) (Y s 3)) t := by
    unfold matchingPhaseSlope
    fun_prop
  have hcD : ContinuousAt (fun s => connectionSpeed (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t := by
    unfold connectionSpeed coupling
    fun_prop
  have hca : ContinuousAt (fun s => connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t := by
    unfold connectionStrongClockRate connectionStrongRate
    fun_prop
  have hcW : ContinuousAt (fun s => matchingPhaseWVariation (-Y s 0) (Y s 2) (Y s 3)) t := by
    unfold matchingPhaseWVariation
    exact ((hcoord 3).pow 2).neg.div (hcKm.mul hcf) (mul_ne_zero hKm hf)
  change ContinuousAt (fun s =>
    (-(-Y s 0 + connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) *
      matchingPhaseWVariation (-Y s 0) (Y s 2) (Y s 3) + Y s 3 * (Y s 2 - Y s 3) +
      connectionStrongClockRate (-Y s 0) (Y s 1) (Y s 2) (Y s 3) * Y s 1 * Y s 3) /
      connectionSpeed (-Y s 0) (Y s 1) (Y s 2) (Y s 3)) t
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_connectionGrowingSources {Y : ℝ → ProjectiveState} {μ w a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    (∫ z in a..b, connectionGrowingStrongSource μ w (Y z)) =
      (32 / (μ * w)) * ((∫ z in a..b, Y z 3 ^ 2) + ∫ z in a..b, Y z 2 * Y z 3) +
        (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ w (Y z)) =
      (64 / (μ * w)) * (∫ z in a..b, Y z 3 ^ 2) + (64 * μ / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ w (Y z)) =
      (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) +
        (32 / (μ ^ 3 * w)) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) := by
  have hW : IntervalIntegrable (fun z => Y z 3 ^ 2) volume a b :=
    ((continuousOn_pi.mp hc 3).pow 2).intervalIntegrable_of_Icc hab
  have hP : IntervalIntegrable (fun z => Y z 2 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hUW : IntervalIntegrable (fun z => Y z 1 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 1).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hP2 : IntervalIntegrable (fun z => (Y z 2 * Y z 3) ^ 2) volume a b :=
    (((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).pow 2).intervalIntegrable_of_Icc hab
  have hadd (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
      (c d : ℝ) : (∫ z in a..b, c * f z + d * g z) = c * (∫ z in a..b, f z) + d * ∫ z in a..b, g z := by
    rw [intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d)]
    simp only [intervalIntegral.integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ∫ z in a..b, (32 / (μ * w)) * (Y z 3 ^ 2 + Y z 2 * Y z 3) + (32 / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingStrongSource
        ring
      _ = _ := by rw [hadd _ _ (hW.add hP) hUW, intervalIntegral.integral_add hW hP]
  · calc
      _ = ∫ z in a..b, (64 / (μ * w)) * Y z 3 ^ 2 + (64 * μ / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingWeakSource
        ring
      _ = _ := hadd _ _ hW hUW _ _
  · calc
      _ = ∫ z in a..b, (32 / w) * (Y z 1 * Y z 3) + (32 / (μ ^ 3 * w)) * (Y z 2 * Y z 3) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingPhaseSource
        ring
      _ = _ := hadd _ _ hUW hP2 _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_growing_source_integrals {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    (∫ z in a..b, connectionGrowingStrongSource μ (Y a 3) (Y z)) ≤
      32 * (1 + Y b 3 ^ 2 / (μ * Y a 3)) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ (Y a 3) (Y z)) ≤
      256 * Y a 1 + 32 * Y b 3 ^ 2 / (μ * Y a 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ (Y a 3) (Y z)) ≤
      128 * Y a 1 / μ + 8 * Y a 3 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc := HasDerivAt.continuousOn hY
  have HI := integral_connectionGrowingSources (μ := μ) (w := Y a 3) hab hc
  have HM := connectionLog_growing_moments hab hμ hY hm hu hv hw hentry
  have HP := (connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry).2.2.1
  rw [HI.1, HI.2.1, HI.2.2]
  refine ⟨?_, ?_, ?_⟩
  · have H := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add HM.1 HM.2.2.2.1) (by positivity : 0 ≤ 32 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
    have hid : (32 / (μ * Y a 3)) * (Y b 3 ^ 2 / 2 + μ * (Y a 2 * Y a 3) / 2) +
        (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) =
          16 * (Y b 3 ^ 2 / (μ * Y a 3)) + 16 * Y a 2 + 128 * Y a 1 / μ := by field_simp; ring
    rw [hid] at H
    have huμ : 128 * Y a 1 / μ ≤ 1 := (div_le_iff₀ hμ0).mpr (by linarith only [(hu a ha).2, hμ])
    have hq : 0 ≤ Y b 3 ^ 2 / (μ * Y a 3) := by positivity
    linarith only [H, huμ, (hv a ha).2, hq]
  · apply (add_le_add (mul_le_mul_of_nonneg_left HM.1 (by positivity : 0 ≤ 64 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 64 * μ / Y a 3))).trans_eq
    field_simp
    ring
  · have H := add_le_add (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
      (mul_le_mul_of_nonneg_left HP (by positivity : 0 ≤ 32 / (μ ^ 3 * Y a 3)))
    have hid : (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) +
        (32 / (μ ^ 3 * Y a 3)) * (μ * (Y a 2 * Y a 3) ^ 2 / 4) =
          128 * Y a 1 / μ + (8 * Y a 3 / μ ^ 2) * Y a 2 ^ 2 := by field_simp; ring
    rw [hid] at H
    have hv2 : Y a 2 ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (hv a ha).1.le (hv a ha).2 2
    exact H.trans (add_le_add (le_refl _)
      ((mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ 8 * Y a 3 / μ ^ 2)).trans_eq (mul_one _)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionShiftedTangent_component_bounds {μ x R : ℝ} {d : Fin 4 → ℝ}
    (hμ : 0 < μ) (hbound : ‖connectionWeightedTangent μ d - ![x, 0]‖ ≤ R) :
    |d 1| ≤ |x| + R ∧ |d 2| ≤ R / μ ^ 2 := by
  have hx : |d 1 - x| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 0).trans hbound
  have hy : μ ^ 2 * |d 2| ≤ R := by
    simpa [connectionWeightedTangent, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg μ)] using
      (norm_le_pi_norm (connectionWeightedTangent μ d - ![x, 0]) 1).trans hbound
  refine ⟨?_, (le_div_iff₀ (sq_pos_of_pos hμ)).mpr (by simpa only [mul_comm] using hy)⟩
  have H : |d 1| ≤ |d 1 - x| + |x| := by simpa using abs_add_le (d 1 - x) x
  linarith only [H, hx]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_connectionGrowingPrimitive {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    ∃ F : ℝ → ℝ, F a = 0 ∧
      (∀ z ∈ Icc a b, HasDerivAt F (connectionStrongClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3) z) ∧
      ∀ z ∈ Icc a b, |F z| ≤ 32 * (1 + Y z 3 ^ 2 / (μ * Y a 3)) := by
  let g : ℝ → ℝ := fun z => connectionStrongClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3
  have hg : ContinuousOn g (Icc a b) := by
    intro z hz
    have hv' : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
    have hD : connectionSpeed (-Y z 0) (Y z 1) (Y z 2) (Y z 3) ≠ 0 := by
      have H := (connection_speed_bounds hμ (hm z hz) (hu z hz) hv' (hw z hz)).1
      linarith only [H, hμ]
    have hf : matchingPhaseSlope (-Y z 0) (Y z 2) (Y z 3) ≠ 0 := by
      have H := (matchingPhase_slope_bounds hμ (hm z hz) hv' (hw z hz)).1
      linarith only [H]
    exact ((continuousAt_connectionStrongWallColumn (hY z hz).continuousAt
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) hD hf).div_const (Y a 3)).continuousWithinAt
  let G : ℝ → ℝ := fun z => g (projIcc a b hab z)
  let F : ℝ → ℝ := fun t => ∫ z in a..t, G z
  have hG : Continuous G := hg.domRestrict.comp continuous_projIcc
  have hF0 : F a = 0 := by simp [F]
  have hF (z : ℝ) (hz : z ∈ Icc a b) : HasDerivAt F (g z) z := by
    have H := intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a z)
      hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
    simpa only [G, projIcc_of_mem hab hz] using H
  refine ⟨F, hF0, hF, ?_⟩
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hR := (continuous_connectionGrowingSources μ (Y a 3)).1.comp_continuousOn (HasDerivAt.continuousOn hY)
  have H := abs_sub_le_integral_bound ht.1 (fun z hz => hF z (hsub hz)) (hR.mono hsub)
    (fun z hz => (connectionGrowingSources_bound hμ hw0 (hm z (hsub hz)) (hu z (hsub hz))
      ⟨(hv z (hsub hz)).1.le, (hv z (hsub hz)).2⟩ (hw z (hsub hz))).1)
  rw [hF0, sub_zero] at H
  exact H.trans (connectionLog_growing_source_integrals ht.1 hμ (fun z hz => hY z (hsub hz))
    (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
    (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0).1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.connectionLog_growing_primitive_transfer {Y : ℝ → ProjectiveState} {F : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) (hF : ContinuousOn F (Icc a b))
    (hbound : ∀ z ∈ Icc a b, |F z| ≤ 32 * (1 + Y z 3 ^ 2 / (μ * Y a 3))) :
    (∫ z in a..b, 64 * μ * Y z 1 * |F z|) ≤ 6144 * Y a 1 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := HasDerivAt.continuousOn hY
  have hU : ContinuousOn (fun z => Y z 1) (Icc a b) := continuousOn_pi.mp hc 1
  have hUW : ContinuousOn (fun z => Y z 1 * Y z 3 ^ 2) (Icc a b) := hU.mul ((continuousOn_pi.mp hc 3).pow 2)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab
    (((hU.const_mul (64 * μ)).mul hF.abs).intervalIntegrable_of_Icc hab)
    (((hU.const_mul (2048 * μ)).add (hUW.const_mul (2048 / Y a 3))).intervalIntegrable_of_Icc hab)
    (fun z hz => ?_)
  · simp only [Pi.add_apply, Pi.mul_apply] at HI
    rw [intervalIntegral.integral_add ((hU.const_mul _).intervalIntegrable_of_Icc hab)
      ((hUW.const_mul _).intervalIntegrable_of_Icc hab), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at HI
    have HU := (connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry).1
    have HUW := (connectionLog_growing_moments hab hμ hY hm hu hv hw hentry).2.2.1
    apply HI.trans ((add_le_add (mul_le_mul_of_nonneg_left HU (by positivity : 0 ≤ 2048 * μ))
      (mul_le_mul_of_nonneg_left HUW (by positivity : 0 ≤ 2048 / Y a 3))).trans_eq ?_)
    field_simp
    ring
  · have hu0 := (hu z hz).1
    apply (mul_le_mul_of_nonneg_left (hbound z hz) (by positivity : 0 ≤ 64 * μ * Y z 1)).trans_eq
    dsimp
    field_simp
    ring

end
end

private theorem BianchiIX.hasDerivAt_connectionGrowingResidual {D : ℝ → (Fin 4 → ℝ)} {F : ℝ → ℝ}
    {y : ProjectiveState} {μ w t : ℝ} (hμ : μ ≠ 0)
    (hD : HasDerivAt D (connectionLogLinearizedRates y (D t)) t)
    (hF : HasDerivAt F (connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w) t)
    (hζ : D t 3 = 1 / w) :
    HasDerivAt (fun s => connectionWeightedTangent μ (D s) - ![F s, 0])
      ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec
        (connectionWeightedTangent μ (D t) - ![F t, 0]) +
        ((connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec ![F t, 0] +
          ![0, μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w] +
          D t 0 • connectionPhaseColumn μ y)) t := by
  have hvec : HasDerivAt (fun s => ![F s, (0 : ℝ)])
      ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hF
    · exact hasDerivAt_const _ _
  have hwall : (1 / w) • connectionWallColumn μ y -
      ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0] =
      ![0, μ ^ 2 * connectionWeakClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w] := by
    ext i
    fin_cases i <;> simp [connectionWallColumn, div_eq_mul_inv, mul_comm]
  apply ((hasDerivAt_connectionWeightedTangent (Y := fun _ => y) hμ hD).sub hvec).congr_deriv
  rw [hζ, Matrix.mulVec_sub]
  calc
    _ = (connectionTransverseMatrix μ (-y 0) (y 1) (y 2) (y 3)).mulVec (connectionWeightedTangent μ (D t)) +
        ((1 / w) • connectionWallColumn μ y -
          ![connectionStrongClockPartials (-y 0) (y 1) (y 2) (y 3) 3 / w, 0]) +
        D t 0 • connectionPhaseColumn μ y := by abel
    _ = _ := by rw [hwall]; abel

/-- The weak response keeps the entry amplitude after subtracting the strong-source primitive. -/
theorem solution {Y : ℝ → ProjectiveState} {D : ℝ → (Fin 4 → ℝ)}
    {μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000)
    (hw0 : 0 < Y a 3)
    (hD : ∀ z ∈ Icc a b, HasDerivAt D (connectionLogLinearizedRates (Y z) (D z)) z)
    (hζ : ∀ z ∈ Icc a b, D z 3 = 1 / Y a 3) (hx0 : D a 1 = 0) (hy0 : D a 2 = 0) :
    ∀ t ∈ Icc a b,
      |D t 1| ≤ 32 + 12800 * Y a 1 + 96 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|) ∧
      |D t 2| ≤ (12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|)) / μ ^ 2 := by
  obtain ⟨F, hF0, hF, hFbound⟩ := exists_connectionGrowingPrimitive hab hμ hY hm hu hv hw hentry hw0
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hcY := HasDerivAt.continuousOn hY
  have hcD := HasDerivAt.continuousOn hD
  have hcF := HasDerivAt.continuousOn hF
  have hU := continuousOn_pi.mp hcY 1
  have hweak := (continuous_connectionGrowingSources μ (Y a 3)).2.1.comp_continuousOn hcY
  have hZ := (continuousOn_pi.mp hcD 0).abs
  let R : ℝ → ℝ := fun z => 64 * μ * Y z 1 * |F z| +
    connectionGrowingWeakSource μ (Y a 3) (Y z) + 64 * |D z 0|
  have hR : ContinuousOn R (Icc a b) :=
    (((hU.const_mul (64 * μ)).mul hcF.abs).add hweak).add (hZ.const_mul 64)
  have hzero : connectionWeightedTangent μ (D a) - ![F a, 0] = 0 := by
    ext i
    fin_cases i <;> simp [connectionWeightedTangent, hx0, hy0, hF0]
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have H := connectionLog_transverse_forced (ξ := fun z => connectionWeightedTangent μ (D z) - ![F z, 0])
    (R := R) hab hμ hY hm hu hv hw hentry hsmall hwall ⟨le_rfl, hab⟩ ht ht.1
    (fun z hz => hasDerivAt_connectionGrowingResidual (ne_of_gt hμ0) (hD z (hsub hz)) (hF z (hsub hz)) (hζ z (hsub hz)))
    (hR.mono hsub) (fun z hz => ?_)
  · rw [hzero, norm_zero, zero_add] at H
    have h1 : IntervalIntegrable (fun z => 64 * μ * Y z 1 * |F z|) volume a t :=
      (((hU.const_mul (64 * μ)).mul hcF.abs).mono hsub).intervalIntegrable_of_Icc ht.1
    have h2 : IntervalIntegrable (fun z => connectionGrowingWeakSource μ (Y a 3) (Y z)) volume a t :=
      (hweak.mono hsub).intervalIntegrable_of_Icc ht.1
    have h3 := ((hZ.const_mul 64).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    dsimp [R] at H
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul] at H
    have HF := connectionLog_growing_primitive_transfer ht.1 hμ (fun z hz => hY z (hsub hz))
      (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
      (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0
      (hcF.mono hsub) (fun z hz => hFbound z (hsub hz))
    have HW := (connectionLog_growing_source_integrals ht.1 hμ (fun z hz => hY z (hsub hz))
      (fun z hz => hm z (hsub hz)) (fun z hz => hu z (hsub hz))
      (fun z hz => hv z (hsub hz)) (fun z hz => hw z (hsub hz)) hentry hw0).2.1
    have HR : ‖connectionWeightedTangent μ (D t) - ![F t, 0]‖ ≤
        12800 * Y a 1 + 64 * Y t 3 ^ 2 / (μ * Y a 3) + 128 * (∫ z in a..t, |D z 0|) := by
      apply H.trans
      exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add HF HW) (le_refl _))
        (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
    have HC := connectionShiftedTangent_component_bounds hμ0 HR
    exact ⟨HC.1.trans ((add_le_add (hFbound t ht) (le_refl _)).trans_eq (by ring)), HC.2⟩
  · have hz' := hsub hz
    have hv' : 0 ≤ Y z 2 ∧ Y z 2 ≤ 1 := ⟨(hv z hz').1.le, (hv z hz').2⟩
    have hweak0 := (connectionGrowingSources_nonneg hμ0.le hw0.le (hu z hz').1 hv'.1 (hw z hz').1).2.1
    have hweakNorm : ‖![0, μ ^ 2 * connectionWeakClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3]‖ ≤
        connectionGrowingWeakSource μ (Y a 3) (Y z) := by
      apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      fin_cases i
      · simpa using hweak0
      · change ‖μ ^ 2 * connectionWeakClockPartials (-Y z 0) (Y z 1) (Y z 2) (Y z 3) 3 / Y a 3‖ ≤ _
        simpa only [Real.norm_eq_abs] using
          (connectionGrowingSources_bound hμ hw0 (hm z hz') (hu z hz') hv' (hw z hz')).2.1
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (add_le_add
        (connectionTransverseMatrix_strong_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') (F z)) hweakNorm)
    · exact connectionPhaseColumn_forcing hμ (hm z hz') (hu z hz') hv' (hw z hz') (D z 0)
