-- Prove2me | solution 1 for GRH.nonprincipal_corrected_prime_ramp_abs_le_of_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:06:16.359174+00:00
-- url     : https://prove2.me/submissions/ab820e35-ff6d-4bc1-a87d-c845e4d752c4

import Mathlib
import Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_partial_fraction
import Theorems.Thm_Zeta23_Analytic_residueTheorem_finset

/-!
# The corrected Dirichlet prime ramp at a zero-free boundary

Davenport's local partial fractions are integrated over a fixed half-height
band. The simple poles are integrable in two real dimensions. Fubini
selects a vertical edge and horizontal heights. Finite rectangle residues
and the inverse Laplace identity then give a bound at the boundary exponent.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Complex Set Finset Filter Topology Metric MeasureTheory
open scoped Interval Classical

noncomputable section

namespace MasulloDirichletEndpoint

def ordinate (k : ℤ) : ℝ := (k:ℝ)/2

def band (k : ℤ) : Set ℝ := Icc (ordinate k - 1/4) (ordinate k + 1/4)

def bandIndex (t : ℝ) : ℤ := ⌊2*t+1/2⌋

theorem mem_band_bandIndex (t : ℝ) : t ∈ band (bandIndex t) := by
  have h₁ := Int.floor_le (2*t+1/2)
  have h₂ := Int.lt_floor_add_one (2*t+1/2)
  change ordinate (bandIndex t)-1/4 ≤ t ∧ t ≤ ordinate (bandIndex t)+1/4
  dsimp only [ordinate,bandIndex]
  constructor <;> linarith

def strip : Set ℂ := Icc (2/3:ℝ) 3 ×ℂ (univ : Set ℝ)

def bandRect (k : ℤ) : Set ℂ := Icc (2/3:ℝ) 3 ×ℂ band k

def center (k : ℤ) : ℂ := 2 + (ordinate k:ℂ)*I

@[simp] theorem center_re (k : ℤ) : (center k).re = 2 := by simp [center]
@[simp] theorem center_im (k : ℤ) : (center k).im = ordinate k := by simp [center]

theorem bandRect_measurable (k : ℤ) : MeasurableSet (bandRect k) := by
  change MeasurableSet (Complex.re ⁻¹' Icc (2/3:ℝ) 3 ∩ Complex.im ⁻¹' band k)
  exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
    (measurableSet_Icc.preimage Complex.continuous_im.measurable)

theorem bandRect_union : (⋃ k : ℤ, bandRect k) = strip := by
  ext z
  simp only [Set.mem_iUnion,bandRect,strip,Complex.mem_reProdIm,Set.mem_univ,and_true]
  exact ⟨fun ⟨_,hk⟩ => hk.1,fun hz => ⟨bandIndex z.im,hz,mem_band_bandIndex z.im⟩⟩

theorem bandRect_subset_ball (k : ℤ) :
    bandRect k ⊆ closedBall (center k) (7/5) := by
  intro z hz
  obtain ⟨hr,hi⟩ := Complex.mem_reProdIm.mp hz
  have hr₁ : (2/3:ℝ) ≤ z.re := hr.1
  have hr₂ : z.re ≤ 3 := hr.2
  have hi₁ : ordinate k-1/4 ≤ z.im := hi.1
  have hi₂ : z.im ≤ ordinate k+1/4 := hi.2
  have hs : (z.re-2)^2 ≤ (4/3:ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (4/3:ℝ)-(z.re-2) by linarith)
      (show 0 ≤ (4/3:ℝ)+(z.re-2) by linarith)]
  have ht : (z.im-ordinate k)^2 ≤ (1/4:ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (1/4:ℝ)-(z.im-ordinate k) by linarith)
      (show 0 ≤ (1/4:ℝ)+(z.im-ordinate k) by linarith)]
  have hSq : ‖z-center k‖^2 = (z.re-2)^2+(z.im-ordinate k)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  rw [Metric.mem_closedBall,dist_eq_norm]
  nlinarith [norm_nonneg (z-center k)]

theorem bandRect_subset_ball_of_mem_larger {k : ℤ} {ρ : ℂ}
    (hρ : ρ ∈ closedBall (center k) (3/2)) :
    bandRect k ⊆ ball ρ 3 := by
  intro z hz
  have hA := (Metric.mem_closedBall.mp (bandRect_subset_ball k hz))
  have hB := Metric.mem_closedBall.mp hρ
  exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_triangle_right z ρ (center k)) (by linarith))

def quadraticWeight (t : ℝ) : ℝ := (1+|t|)^(-2:ℝ)

theorem quadraticWeight_nonneg (t : ℝ) : 0 ≤ quadraticWeight t := by
  unfold quadraticWeight
  positivity

theorem quadraticWeight_on_band {k : ℤ} {t : ℝ} (ht : t ∈ band k) :
    quadraticWeight t ≤ 4*(1+|(k:ℝ)|)^(-2:ℝ) := by
  have h₁ : ordinate k-1/4 ≤ t := ht.1
  have h₂ : t ≤ ordinate k+1/4 := ht.2
  have hD : |(k:ℝ)-2*t| ≤ 1/2 := by
    dsimp [ordinate] at h₁ h₂
    rw [abs_le]
    constructor <;> linarith
  have hTR := abs_add_le ((k:ℝ)-2*t) (2*t)
  rw [sub_add_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hTR
  have hLower : (1+|(k:ℝ)|)/2 ≤ 1+|t| := by linarith
  have hPos : 0 < (1+|(k:ℝ)|)/2 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos hPos hLower (show (-2:ℝ) ≤ 0 by norm_num)
  rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2)] at h
  have hh : (2:ℝ)^(-2:ℝ) = 1/4 := by norm_num [Real.rpow_neg,Real.rpow_two]
  rw [hh] at h
  exact h.trans_eq (by ring)

private theorem reciprocal_norm_integrable_origin :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (ball 0 3) volume := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; norm_num)
  · exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.rpow_neg_one,one_mul])
  · exact (continuous_norm.measurable.inv).aestronglyMeasurable

def inverseDiskMass : ℝ := ∫ z : ℂ in ball 0 3, ‖z‖⁻¹

theorem inverseDiskMass_nonneg : 0 ≤ inverseDiskMass :=
  integral_nonneg fun _ => inv_nonneg.mpr (norm_nonneg _)

private theorem translated_reciprocal_integral (ρ : ℂ) :
    IntegrableOn (fun z : ℂ => ‖z-ρ‖⁻¹) (ball ρ 3) volume ∧
    (∫ z : ℂ in ball ρ 3, ‖z-ρ‖⁻¹) = inverseDiskMass := by
  let e := MeasurableEquiv.subRight ρ
  have hM : MeasurePreserving e (volume : Measure ℂ) volume :=
    measurePreserving_sub_right volume ρ
  have hS : e ⁻¹' ball 0 (3:ℝ) = ball ρ 3 := by
    ext z
    change z-(_ : ℂ) ∈ ball 0 3 ↔ _
    simp [Metric.mem_ball,dist_eq_norm]
  constructor
  · have h := (hM.integrableOn_comp_preimage e.measurableEmbedding).mpr reciprocal_norm_integrable_origin
    rw [hS] at h
    exact h
  · have h := hM.setIntegral_preimage_emb e.measurableEmbedding (fun z : ℂ => ‖z‖⁻¹) (ball 0 3)
    rw [hS] at h
    exact h

theorem reciprocal_band_integrable {k : ℤ} {ρ : ℂ} (hρ : ρ ∈ closedBall (center k) (3/2)) :
    IntegrableOn (fun z : ℂ => ‖z-ρ‖⁻¹) (bandRect k) ∧
      (∫ z : ℂ in bandRect k, ‖z-ρ‖⁻¹) ≤ inverseDiskMass := by
  obtain ⟨hi,he⟩ := translated_reciprocal_integral ρ
  have hS := bandRect_subset_ball_of_mem_larger hρ
  refine ⟨hi.mono_set hS,?_⟩
  rw [← he]
  exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => by positivity)) (Eventually.of_forall hS)

def diskArea : ℝ := (volume : Measure ℂ).real (ball 0 3)

theorem diskArea_nonneg : 0 ≤ diskArea := ENNReal.toReal_nonneg

theorem bandRect_volume_le (k : ℤ) :
    (volume : Measure ℂ).real (bandRect k) ≤ diskArea := by
  have hS : bandRect k ⊆ ball (center k) 3 :=
    (bandRect_subset_ball k).trans (closedBall_subset_ball (by norm_num))
  refine (measureReal_mono hS (by finiteness)).trans_eq ?_
  let e := MeasurableEquiv.subRight (center k)
  have hM : MeasurePreserving e (volume : Measure ℂ) volume :=
    measurePreserving_sub_right volume _
  have he : e ⁻¹' ball 0 (3:ℝ) = ball (center k) 3 := by
    ext z
    change z-(_ : ℂ) ∈ ball 0 3 ↔ _
    simp [Metric.mem_ball,dist_eq_norm]
  have hEq := hM.measure_preimage (measurableSet_ball (x := (0:ℂ)) (ε := (3:ℝ))).nullMeasurableSet
  rw [he] at hEq
  simp only [diskArea,measureReal_def,hEq]


private theorem measurable_logDeriv {f : ℂ → ℂ} (hf : Measurable f) :
    Measurable (logDeriv f) :=
  (measurable_deriv f).div hf

def weightedLogDeriv (f : ℂ → ℂ) (z : ℂ) : ℝ := quadraticWeight z.im * ‖logDeriv f z‖

private theorem weightedLogDeriv_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ weightedLogDeriv f z :=
  mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _)

private theorem weightedLogDeriv_measurable {f : ℂ → ℂ} (hf : Measurable f) :
    Measurable (weightedLogDeriv f) := by
  refine Measurable.mul ?_ (measurable_logDeriv hf).norm
  exact (measurable_const.add Complex.continuous_im.measurable.abs).pow_const _

def multiplicity (f : ℂ → ℂ) (ρ : ℂ) : ℝ := (analyticOrderNatAt f ρ : ℝ)

theorem multiplicity_nonneg (f : ℂ → ℂ) (ρ : ℂ) : 0 ≤ multiplicity f ρ := by
  unfold multiplicity
  positivity

def localPoleNorms (f : ℂ → ℂ) (Z : Finset ℂ) (z : ℂ) : ℝ :=
  ∑ ρ ∈ Z, multiplicity f ρ * ‖z-ρ‖⁻¹

private theorem localPoleNorms_nonneg (f : ℂ → ℂ) (Z : Finset ℂ) (z : ℂ) :
    0 ≤ localPoleNorms f Z z :=
  Finset.sum_nonneg (fun ρ _ => mul_nonneg (multiplicity_nonneg f ρ) (by positivity))

def BandZeroDatum (f : ℂ → ℂ) (Z : Finset ℂ) (k : ℤ) (A : ℝ) : Prop :=
  (Z : Set ℂ) = {ρ ∈ closedBall (center k) (3/2) | f ρ = 0} ∧
    (∑ ρ ∈ Z, multiplicity f ρ) ≤ A ∧
    ∀ s ∈ closedBall (center k) (7/5), f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ)/(s-ρ)‖ ≤ A

theorem dirichlet_band_zero_data {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z : ℤ → Finset ℂ,
      ∀ k : ℤ, BandZeroDatum χ.LFunction (Z k) k (C*Real.log ((q:ℝ)*(|ordinate k|+2))) := by
  obtain ⟨C,hC,h⟩ := SWPort.Davenport.logDeriv_LFunction_partial_fraction
  choose Z hZ using fun k : ℤ => h q χ hχ (ordinate k)
  exact ⟨C,hC,Z,fun k => hZ k⟩

theorem norm_logDeriv_le_band {f : ℂ → ℂ} {Z : Finset ℂ} {k : ℤ} {A : ℝ}
    (hZ : BandZeroDatum f Z k A) {z : ℂ} (hz : z ∈ bandRect k) :
    ‖logDeriv f z‖ ≤ A + localPoleNorms f Z z := by
  have hA : 0 ≤ A := (Finset.sum_nonneg (fun ρ _ => multiplicity_nonneg f ρ)).trans hZ.2.1
  by_cases hf : f z = 0
  · simpa only [logDeriv,Pi.div_apply,hf,div_zero,norm_zero] using add_nonneg hA (localPoleNorms_nonneg f Z z)
  let S := ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ)/(z-ρ)
  have hR : ‖logDeriv f z - S‖ ≤ A := hZ.2.2 z (bandRect_subset_ball k hz) hf
  calc
    ‖logDeriv f z‖ = ‖(logDeriv f z-S)+S‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv f z-S‖+‖S‖ := norm_add_le _ _
    _ ≤ A+localPoleNorms f Z z := by
      apply add_le_add hR
      apply (norm_sum_le _ _).trans
      unfold localPoleNorms
      apply Finset.sum_le_sum
      intro ρ _
      rw [norm_div,Complex.norm_natCast,div_eq_mul_inv,multiplicity]

theorem weightedLogDeriv_band_integral {f : ℂ → ℂ} (hf : Measurable f)
    {Z : Finset ℂ} {k : ℤ} {A : ℝ} (hZ : BandZeroDatum f Z k A) :
    IntegrableOn (weightedLogDeriv f) (bandRect k) ∧
      (∫ z : ℂ in bandRect k, ‖weightedLogDeriv f z‖) ≤
        (4*(1+|(k:ℝ)|)^(-2:ℝ))*A*(diskArea+inverseDiskMass) := by
  let μ := (volume : Measure ℂ).restrict (bandRect k)
  let W : ℝ := 4*(1+|(k:ℝ)|)^(-2:ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 ≤ A := (Finset.sum_nonneg (fun ρ _ => multiplicity_nonneg f ρ)).trans hZ.2.1
  have hzBall (ρ : ℂ) (hρ : ρ ∈ Z) : ρ ∈ closedBall (center k) (3/2) :=
    (show ρ ∈ {ρ ∈ closedBall (center k) (3/2) | f ρ = 0} from hZ.1 ▸ hρ).1
  have hP (ρ : ℂ) (hρ : ρ ∈ Z) :
      Integrable (fun z : ℂ => multiplicity f ρ * ‖z-ρ‖⁻¹) μ :=
    (reciprocal_band_integrable (hzBall ρ hρ)).1.const_mul _
  have hL : Integrable (localPoleNorms f Z) μ := integrable_finsetSum _ hP
  have hS : bandRect k ⊆ ball (center k) 3 :=
    (bandRect_subset_ball k).trans (closedBall_subset_ball (by norm_num))
  have hFin : (volume : Measure ℂ) (bandRect k) ≠ ⊤ := measure_ne_top_of_subset hS (by finiteness)
  have hConst : Integrable (fun _ : ℂ => A) μ := integrableOn_const hFin
  have hDom : Integrable (fun z : ℂ => W*(A+localPoleNorms f Z z)) μ :=
    (hConst.add hL).const_mul _
  have hPt : ∀ᵐ z ∂μ, ‖weightedLogDeriv f z‖ ≤ W*(A+localPoleNorms f Z z) := by
    filter_upwards [ae_restrict_mem (bandRect_measurable k)] with z hz
    rw [Real.norm_of_nonneg (weightedLogDeriv_nonneg f z)]
    exact mul_le_mul (quadraticWeight_on_band ((Complex.mem_reProdIm.mp hz).2))
      (norm_logDeriv_le_band hZ hz) (norm_nonneg _) hW
  have hF : Integrable (weightedLogDeriv f) μ :=
    hDom.mono' (weightedLogDeriv_measurable hf).aestronglyMeasurable hPt
  refine ⟨hF,(integral_mono_ae hF.norm hDom hPt).trans ?_⟩
  have hWbound : ∫ z : ℂ, localPoleNorms f Z z ∂μ ≤ A*inverseDiskMass := by
    unfold localPoleNorms
    rw [integral_finsetSum _ hP]
    calc
      _ ≤ ∑ ρ ∈ Z,multiplicity f ρ*inverseDiskMass := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (reciprocal_band_integrable (hzBall ρ hρ)).2 (multiplicity_nonneg _ _)
      _ = (∑ ρ ∈ Z,multiplicity f ρ)*inverseDiskMass := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hZ.2.1 inverseDiskMass_nonneg
  rw [integral_const_mul,integral_add hConst hL,integral_const]
  simp only [smul_eq_mul]
  rw [show μ.real Set.univ = volume.real (bandRect k) by simp [μ,measureReal_def] ]
  calc
    W*(volume.real (bandRect k)*A + ∫ z : ℂ,localPoleNorms f Z z ∂μ) ≤
        W*(diskArea*A + A*inverseDiskMass) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (bandRect_volume_le k) hA) hWbound) hW
    _ = _ := by ring

theorem band_log_bound {q : ℕ} [NeZero q] {C : ℝ} (hC : 0 ≤ C) (k : ℤ) :
    C*Real.log ((q:ℝ)*(|ordinate k|+2)) ≤ (2*C*Real.sqrt (2*(q:ℝ)))*(1+|(k:ℝ)|)^(1/2:ℝ) := by
  let v := (q:ℝ)*(|ordinate k|+2)
  have hv : 0 < v := mul_pos (by exact_mod_cast NeZero.pos q) (by linarith [abs_nonneg (ordinate k)])
  have hv' : v ≤ 2*(q:ℝ)*(1+|(k:ℝ)|) := by
    dsimp [v,ordinate]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hQ : (0:ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith [mul_nonneg hQ (abs_nonneg (k:ℝ))]
  have hl : Real.log v ≤ 2*Real.sqrt v := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hv)
    rw [Real.log_sqrt hv.le] at h
    linarith
  calc
    C*Real.log v ≤ C*(2*Real.sqrt v) := mul_le_mul_of_nonneg_left hl hC
    _ ≤ C*(2*Real.sqrt (2*(q:ℝ)*(1+|(k:ℝ)|))) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*q),Real.sqrt_eq_rpow (1+|(k:ℝ)|)]
      ring

theorem summable_band_weight : Summable (fun k : ℤ => (1+|(k:ℝ)|)^(-3/2:ℝ)) := by
  have hS := (Real.summable_one_div_int_add_rpow (1/2) (3/2)).mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hS
  intro k
  have hn : 0 < |(k:ℝ)+1/2| := by
    apply abs_pos.mpr
    intro h
    have hK : (0:ℤ) ≤ k ∨ k ≤ -1 := by omega
    rcases hK with hK | hK
    · have hm : (0:ℝ) ≤ k := by exact_mod_cast hK
      linarith
    · have hm : (k:ℝ) ≤ -1 := by exact_mod_cast hK
      linarith
  have hAbs : |(k:ℝ)+1/2| ≤ (1+|(k:ℝ)|) := by
    have h := abs_add_le (k:ℝ) (1/2:ℝ)
    norm_num at h
    linarith
  rw [one_div, ← Real.rpow_neg hn.le,neg_div]
  exact Real.rpow_le_rpow_of_nonpos hn hAbs (show -(3/2:ℝ) ≤ 0 by norm_num)

theorem weighted_logDeriv_integrable_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    IntegrableOn (weightedLogDeriv χ.LFunction) strip := by
  obtain ⟨C,hC,Z,hZ⟩ := dirichlet_band_zero_data χ hχ
  have hf : Measurable χ.LFunction := by
    have hD : Differentiable ℂ χ.LFunction := fun s => χ.differentiableAt_LFunction s (.inr hχ)
    exact hD.continuous.measurable
  have hBand := fun k => weightedLogDeriv_band_integral hf (hZ k)
  rw [← bandRect_union]
  apply integrableOn_iUnion_of_summable_integral_norm (fun k => (hBand k).1)
  let B := 2*C*Real.sqrt (2*(q:ℝ))
  let K := 4*B*(diskArea+inverseDiskMass)
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    _ (summable_band_weight.mul_left K)
  intro k
  let U := 1+|(k:ℝ)|
  have hU : 0 < U := by dsimp [U]; positivity
  refine (hBand k).2.trans ?_
  calc
    _ ≤ (4*U^(-2:ℝ))*(B*U^(1/2:ℝ))*(diskArea+inverseDiskMass) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (band_log_bound (q := q) hC.le k) (by positivity)) (add_nonneg diskArea_nonneg inverseDiskMass_nonneg)
    _ = K*U^(-3/2:ℝ) := by
      have h : U^(-2:ℝ)*U^(1/2:ℝ) = U^(-3/2:ℝ) := by
        rw [← Real.rpow_add hU]
        congr 1
        norm_num
      dsimp only [K]
      linear_combination (4*B*(diskArea+inverseDiskMass))*h

end MasulloDirichletEndpoint

set_option autoImplicit false
set_option maxHeartbeats 1500000

open Complex Set Finset Filter Topology Metric MeasureTheory
open scoped Interval Classical

noncomputable section

namespace MasulloDirichletEndpoint

def point (r t : ℝ) : ℂ := ⟨r,t⟩

@[simp] theorem point_re (r t : ℝ) : (point r t).re = r := rfl
@[simp] theorem point_im (r t : ℝ) : (point r t).im = t := rfl

theorem point_eq (r t : ℝ) : point r t = (r:ℂ)+(t:ℂ)*I := by
  apply Complex.ext <;> simp

def stripZeros (f : ℂ → ℂ) : Set ℂ := {z | z ∈ strip ∧ f z = 0}

theorem stripZeros_mem_band {f : ℂ → ℂ} {Z : ℤ → Finset ℂ} {A : ℤ → ℝ}
    (hZ : ∀ k, BandZeroDatum f (Z k) k (A k)) {z : ℂ} (hz : z ∈ stripZeros f) :
    z ∈ Z (bandIndex z.im) := by
  let k := bandIndex z.im
  have hzRec : z ∈ bandRect k :=
    Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hz.1).1,mem_band_bandIndex z.im⟩
  have h := (bandRect_subset_ball k hzRec)
  have hzBall : z ∈ closedBall (center k) (3/2) := closedBall_subset_closedBall (by norm_num) h
  change z ∈ (Z k : Set ℂ)
  rw [(hZ k).1]
  exact ⟨hzBall,hz.2⟩

theorem stripZeros_countable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (stripZeros χ.LFunction).Countable := by
  obtain ⟨C,_,Z,hZ⟩ := dirichlet_band_zero_data χ hχ
  refine (Set.countable_iUnion (fun k : ℤ => (Z k).finite_toSet.countable)).mono ?_
  intro z hz
  exact Set.mem_iUnion.mpr ⟨bandIndex z.im,stripZeros_mem_band hZ hz⟩

theorem stripZeros_inter_height_finite {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    {z ∈ stripZeros χ.LFunction | |z.im| ≤ T}.Finite := by
  obtain ⟨C,_,Z,hZ⟩ := dirichlet_band_zero_data χ hχ
  let J := Finset.Icc (⌊-2*T-1⌋ : ℤ) (⌊2*T+1⌋ : ℤ)
  apply ((J.biUnion Z).finite_toSet).subset
  intro z hz
  apply Finset.mem_biUnion.mpr
  refine ⟨bandIndex z.im,Finset.mem_Icc.mpr ⟨?_,?_⟩,stripZeros_mem_band hZ hz.1⟩
  · apply Int.floor_mono
    have h := (abs_le.mp hz.2).1
    linarith
  · apply Int.floor_mono
    have h := (abs_le.mp hz.2).2
    linarith

theorem bounded_weighted_zero_sums {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ S : Finset ℂ, (∀ z ∈ S, z ∈ stripZeros χ.LFunction) →
      (∑ z ∈ S, multiplicity χ.LFunction z * quadraticWeight z.im) ≤ M := by
  obtain ⟨C,hC,Z,hZ⟩ := dirichlet_band_zero_data χ hχ
  let A (k : ℤ) : ℝ := C*Real.log ((q:ℝ)*(|ordinate k|+2))
  let w (k : ℤ) : ℝ := (4*(1+|(k:ℝ)|)^(-2:ℝ))*A k
  have hA (k : ℤ) : 0 ≤ A k :=
    (Finset.sum_nonneg (fun z _ => multiplicity_nonneg χ.LFunction z)).trans (hZ k).2.1
  have hw (k : ℤ) : 0 ≤ w k := by dsimp [w]; exact mul_nonneg (by positivity) (hA k)
  have hSum : Summable w := by
    let B := 2*C*Real.sqrt (2*(q:ℝ))
    refine Summable.of_nonneg_of_le hw ?_ (summable_band_weight.mul_left (4*B))
    intro k
    let U := 1+|(k:ℝ)|
    have hU : 0 < U := by dsimp [U]; positivity
    calc
      w k ≤ (4*U^(-2:ℝ))*(B*U^(1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left (band_log_bound (q := q) hC.le k) (by positivity)
      _ = (4*B)*U^(-3/2:ℝ) := by
        have h : U^(-2:ℝ)*U^(1/2:ℝ) = U^(-3/2:ℝ) := by
          rw [← Real.rpow_add hU]
          congr 1
          norm_num
        linear_combination (4*B)*h
  refine ⟨∑' k,w k,tsum_nonneg hw,fun S hS => ?_⟩
  let j (z : ℂ) := bandIndex z.im
  let g (z : ℂ) := multiplicity χ.LFunction z * quadraticWeight z.im
  rw [← Finset.sum_fiberwise_of_maps_to (t := S.image j)
    (fun p hp => Finset.mem_image_of_mem j hp) g]
  calc
    _ ≤ ∑ k ∈ S.image j,w k := by
      apply Finset.sum_le_sum
      intro k _
      let U := S.filter (fun z => j z = k)
      have hZU : U ⊆ Z k := by
        intro z hz
        obtain ⟨hmem,hk⟩ := Finset.mem_filter.mp hz
        rw [← hk]
        exact stripZeros_mem_band hZ (hS z hmem)
      calc
        _ ≤ ∑ z ∈ U,multiplicity χ.LFunction z*(4*(1+|(k:ℝ)|)^(-2:ℝ)) := by
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_mul_of_nonneg_left _ (multiplicity_nonneg _ _)
          have hm := (Finset.mem_filter.mp hz).2
          rw [← hm]
          exact quadraticWeight_on_band (mem_band_bandIndex z.im)
        _ ≤ ∑ z ∈ Z k,multiplicity χ.LFunction z*(4*(1+|(k:ℝ)|)^(-2:ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hZU (fun z _ _ =>
            mul_nonneg (multiplicity_nonneg _ _) (by positivity))
        _ ≤ w k := by
          dsimp only [w]
          rw [← Finset.sum_mul,mul_comm (4*(1+|(k:ℝ)|)^(-2:ℝ))]
          exact mul_le_mul_of_nonneg_right (hZ k).2.1 (by positivity)
    _ ≤ _ := hSum.sum_le_tsum _ (fun k _ => hw k)

theorem integrable_weighted_logDeriv_prod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    Integrable (fun p : ℝ × ℝ => weightedLogDeriv χ.LFunction (point p.1 p.2))
      (((volume : Measure ℝ).restrict (Icc (2/3:ℝ) 3)).prod volume) := by
  let e := Complex.measurableEquivRealProd.symm
  have h := (Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
    e.measurableEmbedding).mpr (weighted_logDeriv_integrable_strip χ hχ)
  change Integrable (fun p : ℝ × ℝ => weightedLogDeriv χ.LFunction (point p.1 p.2))
    ((volume : Measure (ℝ × ℝ)).restrict ((Icc (2/3:ℝ) 3) ×ˢ (Set.univ : Set ℝ))) at h
  rw [Measure.volume_eq_prod,← Measure.prod_restrict,Measure.restrict_univ] at h
  exact h

theorem exists_good_vertical_edge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ a : ℝ, a ∈ Ioo (2/3:ℝ) (3/4) ∧
      (∀ t : ℝ, χ.LFunction (point a t) ≠ 0) ∧
      Integrable (fun t : ℝ => weightedLogDeriv χ.LFunction (point a t)) := by
  let s := Ioo (2/3:ℝ) (3/4)
  let ν := (volume : Measure ℝ).restrict s
  have hMn : ν ≤ (volume : Measure ℝ).restrict (Icc (2/3:ℝ) 3) := by
    apply Measure.restrict_mono _ le_rfl
    intro x hx
    exact ⟨hx.1.le,hx.2.le.trans (by norm_num)⟩
  have hNu : ν ≠ 0 := by
    intro hzero
    have hM : ν Set.univ = 0 := by rw [hzero]; simp
    rw [show ν Set.univ = volume s by simp [ν],Real.volume_Ioo] at hM
    norm_num [s] at hM
  have : NeBot (ae ν) := ae_neBot.mpr hNu
  have hI := ae_mono hMn (integrable_weighted_logDeriv_prod χ hχ).prod_right_ae
  have hC := (stripZeros_countable χ hχ).image Complex.re
  have hE : ∀ᵐ a ∂ν, a ∈ s ∧ a ∉ Complex.re '' stripZeros χ.LFunction ∧
      Integrable (fun t : ℝ => weightedLogDeriv χ.LFunction (point a t)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := (2/3:ℝ)) (b := (3/4:ℝ))),
      hC.ae_notMem ν,hI] with a ha hBad hi
    exact ⟨ha,hBad,hi⟩
  obtain ⟨a,ha,hBad,hi⟩ := hE.exists
  refine ⟨a,ha,fun t hZero => hBad ?_,hi⟩
  exact ⟨point a t,⟨Complex.mem_reProdIm.mpr
    ⟨⟨ha.1.le,ha.2.le.trans (by norm_num)⟩,Set.mem_univ _⟩,hZero⟩,rfl⟩

def horizontalMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∫ r : ℝ in Icc (2/3:ℝ) 3, weightedLogDeriv χ.LFunction (point r t)

theorem horizontalMass_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    0 ≤ horizontalMass χ t :=
  integral_nonneg fun _ => mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _)

theorem horizontalMass_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : Integrable (horizontalMass χ) := by
  have h := (integrable_weighted_logDeriv_prod χ hχ).integral_norm_prod_right
  have hEq : (fun t : ℝ => ∫ r : ℝ in Icc (2/3:ℝ) 3, ‖weightedLogDeriv χ.LFunction (point r t)‖)
      = horizontalMass χ := by
    funext t
    unfold horizontalMass
    apply integral_congr_ae (Eventually.of_forall fun r => ?_)
    exact Real.norm_of_nonneg (mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _))
  simpa only [hEq] using h

private theorem arbitrarily_late_small_outside_countable
    (g : ℝ → ℝ) (hg : Integrable g) (B : Set ℝ) (hB : B.Countable)
    (X ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, X < t ∧ t ∉ B ∧ g t < ε := by
  by_contra! h
  have hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioi X), ‖ε‖ ≤ g t := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := X)),
      hB.ae_notMem ((volume : Measure ℝ).restrict (Ioi X))] with t ht hBad
    rw [Real.norm_of_nonneg hε.le]
    exact h t ht hBad
  have hI : IntegrableOn (fun _ : ℝ => ε) (Ioi X) volume :=
    (hg.integrableOn (s := Ioi X)).mono' aestronglyMeasurable_const hE
  have hContra := (integrableOn_const_iff (C := ε)).mp hI
  rcases hContra with h | h
  · exact hε.ne' (enorm_eq_zero.mp h)
  · exact h.ne Real.volume_Ioi

theorem exists_good_horizontal_edges {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ∃ T : ℕ → ℝ, ∀ n : ℕ, (n:ℝ)+1 < T n ∧
      (∀ r ∈ Icc (2/3:ℝ) 3, χ.LFunction (point r (T n)) ≠ 0 ∧ χ.LFunction (point r (-T n)) ≠ 0) ∧
      horizontalMass χ (T n) + horizontalMass χ (-T n) < 1/((n:ℝ)+1) := by
  let B := Complex.im '' stripZeros χ.LFunction
  have hC : B.Countable := (stripZeros_countable χ hχ).image Complex.im
  have hC' : (B ∪ Neg.neg '' B).Countable := hC.union (hC.image Neg.neg)
  have hI := horizontalMass_integrable χ hχ
  have hN : Integrable (fun t : ℝ => horizontalMass χ (-t)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hI
  let g := fun t : ℝ => horizontalMass χ t + horizontalMass χ (-t)
  have h (n : ℕ) := arbitrarily_late_small_outside_countable g (hI.add hN) _ hC' (n+1) (1/(n+1)) (by positivity)
  choose T hT using h
  refine ⟨T,fun n => ⟨(hT n).1,?_,(hT n).2.2⟩⟩
  intro r hr
  have hz (t : ℝ) (hzero : χ.LFunction (point r t) = 0) : t ∈ B :=
    ⟨point r t,⟨Complex.mem_reProdIm.mpr ⟨hr,Set.mem_univ _⟩,hzero⟩,rfl⟩
  constructor
  · exact fun hZero => (hT n).2.1 (Or.inl (hz _ hZero))
  · exact fun hZero => (hT n).2.1 (Or.inr ⟨-T n,hz _ hZero,neg_neg _⟩)

end MasulloDirichletEndpoint

set_option autoImplicit false
set_option maxHeartbeats 1800000

open Complex Set Finset Filter Topology Metric MeasureTheory Asymptotics
open scoped Interval Classical ComplexConjugate

noncomputable section

namespace MasulloDirichletEndpoint

private theorem logFactor_order_finite {J : ℂ → ℂ} (hJ : Differentiable ℂ J)
    (hJ1 : J 1 ≠ 0) (ρ : ℂ) : analyticOrderAt J ρ ≠ ⊤ := by
  have h : AnalyticOnNhd ℂ J univ := fun s _ => hJ.analyticAt s
  exact h.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1:ℂ)) (mem_univ ρ) (by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hJ1)]
      simp)

private theorem logDerived_eq_order_term {J : ℂ → ℂ} (hJ : Differentiable ℂ J)
    (hJ1 : J 1 ≠ 0) {ρ : ℂ} (hρ : J ρ = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv J s / J s = (analyticOrderNatAt J ρ:ℂ)/(s-ρ) + H s := by
  have hAnalytic : AnalyticAt ℂ J ρ := hJ.analyticAt _
  obtain ⟨F,hF,hFρ,hFactor⟩ := hAnalytic.analyticOrderAt_ne_top.mp (logFactor_order_finite hJ hJ1 ρ)
  let m := analyticOrderNatAt J ρ
  have hm : 0 < m := by
    have hn := hAnalytic.analyticOrderAt_ne_zero.mpr hρ
    rw [← Nat.cast_analyticOrderNatAt (logFactor_order_finite hJ hJ1 ρ)] at hn
    by_contra! h
    apply hn
    change (m:ℕ∞) = 0
    rw [Nat.eq_zero_of_le_zero h, Nat.cast_zero]
  let H := fun s : ℂ => deriv F s / F s
  refine ⟨H,hF.deriv.div hF hFρ,?_⟩
  have hFact : J =ᶠ[𝓝 ρ] fun s => (s-ρ)^m*F s :=
    hFactor.mono (fun _ h => by simpa only [smul_eq_mul] using h)
  have hLoc : ∀ᶠ s : ℂ in 𝓝 ρ, J =ᶠ[𝓝 s] fun z => (z-ρ)^m*F z :=
    eventually_eventually_nhds.mpr hFact
  have hFnear : ∀ᶠ s in 𝓝 ρ, F s ≠ 0 := hF.continuousAt.eventually_ne hFρ
  have ha := hF.eventually_analyticAt
  filter_upwards [hLoc.filter_mono nhdsWithin_le_nhds, hFnear.filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with s hs hFn hAn hsρ
  have hs' : s ≠ ρ := hsρ
  have hdiff : HasDerivAt (fun z : ℂ => (z-ρ)^m) ((m:ℂ)*(s-ρ)^(m-1)) s := by
    have he := (hasDerivAt_pow m (s-ρ)).comp s ((hasDerivAt_id s).sub_const ρ)
    simpa only [Function.comp_def, id_eq, mul_one] using he
  have hequiv : (s-ρ)^m = (s-ρ)^(m-1)*(s-ρ) := by
    conv_lhs => rw [show m = (m-1)+1 by omega, pow_succ]
  rw [hs.deriv_eq, hs.self_of_nhds]
  change deriv ((fun z : ℂ => (z-ρ)^m) * F) s / ((s-ρ)^m * F s) = _
  rw [(hdiff.mul hAn.differentiableAt.hasDerivAt).deriv]
  change (((m:ℂ)*(s-ρ)^(m-1))*F s+(s-ρ)^m*deriv F s)/((s-ρ)^m*F s) =
    (m:ℂ)/(s-ρ)+deriv F s / F s
  rw [hequiv]
  field_simp [hFn, sub_ne_zero.mpr hs', pow_ne_zero _ (sub_ne_zero.mpr hs')]

def rampWeight (y : ℝ) (z : ℂ) : ℂ := -(y:ℂ)^z/(z*(z-1))

def rampIntegrand (f : ℂ → ℂ) (y : ℝ) (z : ℂ) : ℂ := rampWeight y z * logDeriv f z

def rampResidue (f : ℂ → ℂ) (y : ℝ) (z : ℂ) : ℂ :=
  if z = 1 then -(y:ℂ)*logDeriv f 1
  else (analyticOrderNatAt f z:ℂ)*rampWeight y z

theorem analytic_rampWeight {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    AnalyticAt ℂ (rampWeight y) z := by
  let : NeZero (y:ℂ) := ⟨by exact_mod_cast hy.ne'⟩
  have h : AnalyticAt ℂ (fun w : ℂ => (y:ℂ)^w) z :=
    (differentiable_const_cpow_of_neZero (y:ℂ)).analyticAt z
  exact h.neg.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero hz (sub_ne_zero.mpr hz1))

theorem analytic_logDeriv_at {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0) :
    AnalyticAt ℂ (logDeriv f) z :=
  (hf.analyticAt z).deriv.div (hf.analyticAt z) hz

private theorem residue_ne_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0)
    {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hρ₀ : ρ ≠ 0) (hρ₁ : ρ ≠ 1) (hρ : f ρ = 0) :
    ((rampIntegrand f y) - fun s => rampResidue f y ρ/(s-ρ)) =O[𝓝[≠] ρ] (1:ℂ → ℂ) := by
  obtain ⟨H,hH,hRep⟩ := logDerived_eq_order_term hf hf1 hρ
  let m : ℂ := analyticOrderNatAt f ρ
  let W := rampWeight y
  have hAnalytic : AnalyticAt ℂ W ρ := analytic_rampWeight hy hρ₀ hρ₁
  have hSlope : Tendsto (slope W ρ) (𝓝[≠] ρ) (𝓝 (deriv W ρ)) :=
    hAnalytic.differentiableAt.hasDerivAt.tendsto_slope
  have hC : Tendsto (fun s => m * slope W ρ s + W s*H s)
      (𝓝[≠] ρ) (𝓝 (m*deriv W ρ + W ρ*H ρ)) :=
    (hSlope.const_mul m).add ((hAnalytic.continuousAt.mul hH.continuousAt).mono_left nhdsWithin_le_nhds)
  apply (hC.isBigO_one ℂ).congr'
  · filter_upwards [hRep,eventually_mem_nhdsWithin] with s hs hne
    change m*slope W ρ s + W s*H s = W s*(deriv f s/f s) - rampResidue f y ρ/(s-ρ)
    rw [rampResidue,if_neg hρ₁,hs,slope_def_field]
    change _ = W s*(m/(s-ρ)+H s) - m*W ρ/(s-ρ)
    ring
  · exact EventuallyEq.rfl

private theorem residue_at_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0)
    {y : ℝ} (hy : 0 < y) :
    ((rampIntegrand f y) - fun s => rampResidue f y 1/(s-1)) =O[𝓝[≠] (1:ℂ)] (1:ℂ → ℂ) := by
  let W (s : ℂ) := -(y:ℂ)^s * logDeriv f s / s
  let : NeZero (y:ℂ) := ⟨by exact_mod_cast hy.ne'⟩
  have hP : AnalyticAt ℂ (fun s : ℂ => (y:ℂ)^s) 1 :=
    (differentiable_const_cpow_of_neZero (y:ℂ)).analyticAt _
  have hA : AnalyticAt ℂ W 1 :=
    (hP.neg.mul (analytic_logDeriv_at hf hf1)).div analyticAt_id one_ne_zero
  have hSlope := hA.differentiableAt.hasDerivAt.tendsto_slope
  apply (hSlope.isBigO_one ℂ).congr'
  · apply Eventually.of_forall
    intro s
    rw [slope_def_field]
    change (W s-W 1)/(s-1) = rampWeight y s*logDeriv f s-rampResidue f y 1/(s-1)
    rw [show rampResidue f y 1 = -(y:ℂ)*logDeriv f 1 by simp [rampResidue] ]
    dsimp only [W,rampWeight]
    rw [Complex.cpow_one,div_one,sub_div,div_div]
    ring
  · exact EventuallyEq.rfl

theorem rectangle_zero_set_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a T : ℝ} (ha : 2/3 ≤ a) (ha3 : a ≤ 3) (hT : 0 ≤ T) :
    {z ∈ Rectangle (point a (-T)) (point 3 T) | χ.LFunction z = 0}.Finite := by
  apply (stripZeros_inter_height_finite χ hχ T).subset
  intro z hz
  have hR := Complex.mem_reProdIm.mp hz.1
  simp only [point_re,point_im,uIcc_of_le ha3,uIcc_of_le (by linarith : -T ≤ T)] at hR
  exact ⟨⟨Complex.mem_reProdIm.mpr ⟨⟨ha.trans hR.1.1,hR.1.2⟩,Set.mem_univ _⟩,hz.2⟩,
    abs_le.mpr hR.2⟩

private theorem rectangle_mem_nhds {a b T : ℝ} {z : ℂ}
    (hl : a < z.re) (hr : z.re < b) (hlo : -T < z.im) (hup : z.im < T) :
    Rectangle (point a (-T)) (point b T) ∈ 𝓝 z := by
  change {w : ℂ | w.re ∈ uIcc a b ∧ w.im ∈ uIcc (-T) T} ∈ 𝓝 z
  rw [uIcc_of_le (hl.le.trans hr.le),uIcc_of_le (hlo.le.trans hup.le)]
  exact Filter.inter_mem (Complex.continuous_re.continuousAt (Icc_mem_nhds hl hr))
    (Complex.continuous_im.continuousAt (Icc_mem_nhds hlo hup))

theorem ramp_rectangle_residues {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {y a T : ℝ} (hy : 0 < y) (ha : 2/3 ≤ a) (ha₁ : a < 1)
    (hT : 0 < T) (hL : ∀ t : ℝ, χ.LFunction (point a t) ≠ 0)
    (hH : ∀ r ∈ Icc (2/3:ℝ) 3, χ.LFunction (point r T) ≠ 0 ∧ χ.LFunction (point r (-T)) ≠ 0)
    (S : Finset ℂ)
    (hS : (S:Set ℂ) = {z ∈ Rectangle (point a (-T)) (point 3 T) | χ.LFunction z = 0}) :
    RectangleIntegral' (rampIntegrand χ.LFunction y) (point a (-T)) (point 3 T) =
      -(y:ℂ)*logDeriv χ.LFunction 1 + ∑ p ∈ S,rampResidue χ.LFunction y p := by
  let f := χ.LFunction
  let R := Rectangle (point a (-T)) (point 3 T)
  have hD : Differentiable ℂ f := fun z => χ.differentiableAt_LFunction z (.inr hχ)
  have hOne : f 1 ≠ 0 := χ.LFunction_ne_zero_of_re_eq_one Complex.one_re (.inl hχ)
  have h₁ : (1:ℂ) ∉ S := by
    intro h
    apply hOne
    have ht : (1:ℂ) ∈ {z ∈ R | f z = 0} := hS ▸ h
    exact ht.2
  have hB : a ≤ 3 := ha₁.le.trans (by norm_num)
  have hT' : -T ≤ T := by linarith
  have hIn (z : ℂ) (hz : z ∈ R) : (a ≤ z.re ∧ z.re ≤ 3) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
    have h' := Complex.mem_reProdIm.mp hz
    simpa only [point_re,point_im,uIcc_of_le hB,uIcc_of_le hT',Set.mem_Icc] using h'
  have hSZ (z : ℂ) (hz : z ∈ S) : z ∈ R ∧ f z = 0 := by
    have h' : z ∈ {z ∈ R | f z = 0} := hS ▸ hz
    exact h'
  have hN (z : ℂ) (hz : z ∈ R) : z ≠ 0 := Complex.ne_zero_of_re_pos
    ((by norm_num : (0:ℝ) < 2/3).trans_le (ha.trans (hIn z hz).1.1))
  have hMain : RectangleIntegral' (rampIntegrand f y) (point a (-T)) (point 3 T) =
      ∑ p ∈ insert 1 S, rampResidue f y p := by
    apply Zeta23.Analytic.residueTheorem_finset hB hT' (insert 1 S) (rampResidue f y)
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact rectangle_mem_nhds (by simpa using ha₁) (by simp) (by simpa using neg_lt_zero.mpr hT)
          (by simpa using hT)
      · obtain ⟨hpR,hpZ⟩ := hSZ p hp
        obtain ⟨⟨hpa,hp3⟩,⟨hpLo,hpHi⟩⟩ := hIn p hpR
        have hpl : a < p.re := lt_of_le_of_ne hpa fun he => by
          apply hL p.im
          have hEq : point a p.im = p := by apply Complex.ext <;> simp [he]
          rwa [hEq]
        have hpu : p.re < 3 := lt_of_le_of_ne hp3 fun he =>
          χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by rw [he]; norm_num) hpZ
        have hHr := hH p.re ⟨ha.trans hpa,hp3⟩
        have hlow : -T < p.im := lt_of_le_of_ne hpLo fun he => by
          apply hHr.2
          have hEq : point p.re (-T) = p := by apply Complex.ext <;> simp [he]
          rwa [hEq]
        have hhigh : p.im < T := lt_of_le_of_ne hpHi fun he => by
          apply hHr.1
          have hEq : point p.re T = p := by apply Complex.ext <;> simp [he]
          rwa [hEq]
        exact rectangle_mem_nhds hpl hpu hlow hhigh
    · intro p hp
      have hp1 : p ≠ 1 := fun he => hp.2 (by simp [he])
      have hpZ : f p ≠ 0 := fun he => hp.2 (Finset.mem_insert_of_mem (by
        change p ∈ (S:Set ℂ)
        rw [hS]
        exact ⟨hp.1,he⟩))
      exact ((analytic_rampWeight hy (hN p hp.1) hp1).mul
        (analytic_logDeriv_at hD hpZ)).differentiableAt.differentiableWithinAt
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact residue_at_one hD hOne hy
      · obtain ⟨hpR,hpZ⟩ := hSZ p hp
        exact residue_ne_one hD hOne hy (hN p hpR) (fun he => h₁ (he ▸ hp)) hpZ
  rw [Finset.sum_insert h₁,rampResidue,if_pos rfl] at hMain
  exact hMain

end MasulloDirichletEndpoint

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Complex Set Finset ArithmeticFunction MeasureTheory Filter Topology
open scoped FourierTransform

noncomputable section

namespace MasulloDirichletEndpoint

/-- The inverse Laplace integral on a fixed vertical line, in the
normalization with angular frequency and a `1/(2π)` prefactor. -/
theorem vertical_laplace_inversion (g : ℝ → ℂ) (F : ℂ → ℂ) (c : ℝ)
    (hg : IntegrableOn (fun u : ℝ => g u*Complex.exp (-(c:ℂ)*(u:ℂ))) (Ioi 0))
    (hF : ∀ v : ℝ, F ((c:ℂ)+(v:ℂ)*I) =
      ∫ u in Ioi (0:ℝ), g u*Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(u:ℂ)))
    (hi : Integrable (fun v : ℝ => F ((c:ℂ)+(v:ℂ)*I)))
    (u : ℝ) (hu : 0 < u) (hc : ContinuousAt g u) :
    (1/(2*(Real.pi:ℂ)))*(∫ v : ℝ, Complex.exp (((c:ℂ)+(v:ℂ)*I)*(u:ℂ))*F ((c:ℂ)+(v:ℂ)*I)) = g u := by
  let p (x : ℝ) : ℂ := g x * Complex.exp (-(c:ℂ)*(x:ℂ))
  let f : ℝ → ℂ := (Ioi (0:ℝ)).indicator p
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Ioi).mpr hg
  have hcont : ContinuousAt f u := by
    have hp : ContinuousAt p u := hc.mul (by fun_prop)
    apply hp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hu] with t ht
    exact indicator_of_mem ht p
  let k : ℝ := 2*Real.pi
  have hk : 0 < k := by dsimp [k]; positivity
  have hFourier (v : ℝ) : 𝓕 f v = F ((c:ℂ)+((k*v:ℝ):ℂ)*I) := by
    rw [Real.fourier_real_eq_integral_exp_smul,hF]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Ioi (0:ℝ)
    · simp only [f, p, indicator_of_mem ht, smul_eq_mul]
      rw [mul_left_comm (Complex.exp _), ← Complex.exp_add]
      congr 2
      dsimp [k]
      push_cast
      ring
    · simp [f,indicator_of_notMem ht]
  have hfi : Integrable (𝓕 f) := by
    rw [funext hFourier]
    exact hi.comp_mul_left' hk.ne'
  have hInv := hf.fourierInv_fourier_eq hfi hcont
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hInv
  let Fangle (v : ℝ) : ℂ := Complex.exp (((v:ℂ)*I)*(u:ℂ))*F ((c:ℂ)+(v:ℂ)*I)
  have hEq (v : ℝ) : Complex.exp (↑(-2*Real.pi*v*(-u))*I) • (𝓕 f v) = Fangle (k*v) := by
    rw [hFourier]
    simp only [Fangle,smul_eq_mul]
    congr 2
    dsimp [k]
    push_cast
    ring
  simp_rw [hEq] at hInv
  rw [Measure.integral_comp_mul_left Fangle k, abs_of_pos (inv_pos.mpr hk)] at hInv
  dsimp only [f] at hInv
  rw [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu)] at hInv
  have hL : (fun v : ℝ => Complex.exp (((c:ℂ)+(v:ℂ)*I)*(u:ℂ))*F ((c:ℂ)+(v:ℂ)*I)) =
      fun v : ℝ => Complex.exp ((c:ℂ)*(u:ℂ))*Fangle v := by
    funext v
    rw [add_mul,Complex.exp_add]
    simp only [Fangle,mul_assoc]
  rw [hL,integral_const_mul]
  have hE : Complex.exp ((c:ℂ)*(u:ℂ))*(k⁻¹ • ∫ v : ℝ, Fangle v) = g u := by
    rw [hInv]
    dsimp only [p]
    rw [mul_left_comm, ← Complex.exp_add]
    simp
  simpa only [k, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
    one_div, mul_left_comm] using hE

private noncomputable def arithmeticRampWeight (n : ℕ) (x : ℝ) : ℝ := max (x/(n:ℝ)-1) 0

private theorem arithmeticRampWeight_zero_off_range {n : ℕ} {x : ℝ} (h : n ∉ Finset.range (⌊x⌋₊+1)) :
    arithmeticRampWeight n x = 0 := by
  have hn : ⌊x⌋₊+1 ≤ n := by simpa using h
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : x ≤ (n:ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  unfold arithmeticRampWeight
  exact max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx))

private theorem vonMangoldt_le_nat (n : ℕ) : vonMangoldt n ≤ (n:ℝ) :=
  vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))

private noncomputable def rampLaplaceTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (arithmeticRampWeight n (Real.exp u) : ℂ) * Complex.exp (-s*(u:ℂ))

private theorem rampLaplaceTerm_zero (s : ℂ) : rampLaplaceTerm 0 s = 0 := by
  funext u
  simp [rampLaplaceTerm, arithmeticRampWeight]

private theorem rampLaplaceTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (rampLaplaceTerm n s) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [rampLaplaceTerm_zero]
    exact integrable_zero ℝ ℂ ((volume : Measure ℝ).restrict (Ioi 0))
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hdec : 1-s.re < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hdec 0).const_mul ((n:ℝ)⁻¹)
  have hmeas : Measurable (rampLaplaceTerm n s) := by unfold rampLaplaceTerm arithmeticRampWeight; fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have hle : arithmeticRampWeight n (Real.exp u) ≤ Real.exp u/(n:ℝ) :=
    max_le (by linarith) (by positivity)
  have hh : 0 ≤ arithmeticRampWeight n (Real.exp u) := le_max_right _ _
  change ‖rampLaplaceTerm n s u‖ ≤ (n:ℝ)⁻¹*Real.exp ((1-s.re)*u)
  rw [rampLaplaceTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh, Complex.norm_exp, he]
  calc
    _ ≤ (Real.exp u/(n:ℝ)) * Real.exp (-s.re*u) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = (n:ℝ)⁻¹*(Real.exp u*Real.exp (-s.re*u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem rampLaplaceTerm_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), rampLaplaceTerm n s u) = (n:ℂ)^(-s)/(s*(s-1)) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn₁ : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let l := Real.log (n:ℝ)
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hn)
  have hr : (-(s-1)).re < 0 := by simp [Complex.sub_re]; linarith
  have hr' : (-s).re < 0 := by simp; linarith
  let F (u : ℝ) := (n:ℂ)⁻¹*Complex.exp (-(s-1)*(u:ℂ))-Complex.exp (-s*(u:ℂ))
  have he : rampLaplaceTerm n s = (Ioi l).indicator F := by
    funext u
    by_cases hu : u ∈ Ioi l
    · have hx : (n:ℝ) < Real.exp u := by
        simpa [l, Real.exp_log hn₀] using Real.exp_lt_exp.mpr hu
      have hw : 0 ≤ Real.exp u/(n:ℝ)-1 := sub_nonneg.mpr ((one_le_div hn₀).mpr hx.le)
      rw [indicator_of_mem hu, rampLaplaceTerm, arithmeticRampWeight, max_eq_left hw]
      push_cast
      have h : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      dsimp [F]
      rw [h]
      ring
    · have hx : Real.exp u ≤ (n:ℝ) := by
        have h : u ≤ l := le_of_not_gt hu
        simpa [l, Real.exp_log hn₀] using Real.exp_le_exp.mpr h
      rw [indicator_of_notMem hu, rampLaplaceTerm, arithmeticRampWeight,
        max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx)), Complex.ofReal_zero, zero_mul]
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s-1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hl)]
  dsimp [F]
  rw [integral_sub ((integrableOn_exp_mul_complex_Ioi hr l).const_mul _)
    (integrableOn_exp_mul_complex_Ioi hr' l), integral_const_mul,
    integral_exp_mul_complex_Ioi hr, integral_exp_mul_complex_Ioi hr']
  have hcp : Complex.exp (-s*(l:ℂ)) = (n:ℂ)^(-s) := by
    rw [Complex.cpow_def_of_ne_zero hn₁, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn₀.le]
    dsimp [l]
    rw [mul_comm]
  have hex : Complex.exp (-(s-1)*(l:ℂ)) = Complex.exp (-s*(l:ℂ))*(n:ℂ) := by
    rw [show -(s-1)*(l:ℂ) = -s*(l:ℂ)+(l:ℂ) by ring, Complex.exp_add,
      ← Complex.ofReal_exp, show Real.exp l = (n:ℝ) by exact Real.exp_log hn₀,
      Complex.ofReal_natCast]
  rw [hex,hcp]
  field_simp [hs₀,hs₁,hn₁]
  ring

private theorem norm_rampLaplaceTerm_eq_real_cast (n : ℕ) (s : ℂ) (u : ℝ) :
    (‖rampLaplaceTerm n s u‖:ℂ) = rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
  have hre : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have h : 0 ≤ arithmeticRampWeight n (Real.exp u) := le_max_right _ _
  simp only [rampLaplaceTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg h, Complex.norm_exp, hre]
  push_cast
  rfl

private theorem rampLaplaceTerm_integral_norm {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖) =
      (n:ℝ)^(-s.re)/(s.re*(s.re-1)) := by
  apply Complex.ofReal_injective
  have hnorm : ((∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖ : ℝ) : ℂ) =
      ∫ u in Ioi (0:ℝ), rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => norm_rampLaplaceTerm_eq_real_cast n s u)
  rw [hnorm, rampLaplaceTerm_integral hn (by simpa : 1 < ((s.re:ℝ):ℂ).re)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

private noncomputable def weightedRampTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (vonMangoldt n : ℂ) * rampLaplaceTerm n s u

private theorem weightedRampTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (weightedRampTerm n s) (Ioi 0) := (rampLaplaceTerm_integrable hs n).const_mul _

private theorem summable_weightedRamp_integral_norm {s : ℂ} (hs : 2 < s.re) :
    Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖) := by
  let D : ℝ := s.re*(s.re-1)
  have hσ : 1 < s.re := by linarith
  have hD : 0 < D := mul_pos (by linarith) (sub_pos.mpr hσ)
  have hsum : Summable (fun n : ℕ => ((n:ℝ)^(s.re-1))⁻¹ / D) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < s.re-1)).div_const _
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => ?_) hsum
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedRampTerm, div_nonneg, inv_nonneg, Real.rpow_nonneg, hD.le]
  · rw [show (fun u => ‖weightedRampTerm n s u‖) =
        (fun u => vonMangoldt n * ‖rampLaplaceTerm n s u‖) by
      funext u
      rw [weightedRampTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] ]
    rw [integral_const_mul, rampLaplaceTerm_integral_norm (Nat.pos_of_ne_zero hn) hσ]
    have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have h : (n:ℝ)*(n:ℝ)^(-s.re) = ((n:ℝ)^(s.re-1))⁻¹ := by
      conv_lhs => arg 1; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_add hn₀, ← Real.rpow_neg hn₀.le]
      congr 1
      ring
    calc
      _ ≤ (n:ℝ)*((n:ℝ)^(-s.re)/D) :=
        mul_le_mul_of_nonneg_right (vonMangoldt_le_nat n) (by positivity)
      _ = _ := by rw [← mul_div_assoc, h]

private theorem weightedRampTerm_integral {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), weightedRampTerm n s u) =
      LSeries.term (fun k => (vonMangoldt k:ℂ)) s n/(s*(s-1)) := by
  by_cases hn : n = 0
  · simp [hn, weightedRampTerm]
  · unfold weightedRampTerm
    rw [integral_const_mul, rampLaplaceTerm_integral (Nat.pos_of_ne_zero hn) hs,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    ring

def complexPrimeRamp (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ range (⌊y⌋₊+1), (vonMangoldt n:ℂ) * a n * (arithmeticRampWeight n y:ℂ)

private theorem complexPrimeRamp_growth (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖complexPrimeRamp a y‖ ≤ 2*y^2 := by
  have hy₀ : 0 ≤ y := zero_le_one.trans hy
  have hterm (n : ℕ) : vonMangoldt n * arithmeticRampWeight n y ≤ y := by
    by_cases hn : n = 0
    · subst n
      simpa using hy₀
    · have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hnon : 0 ≤ y/(n:ℝ) := div_nonneg hy₀ hn₀.le
      have hl : arithmeticRampWeight n y ≤ y/(n:ℝ) := max_le (by linarith) hnon
      calc
        _ ≤ (n:ℝ)*(y/(n:ℝ)) :=
          mul_le_mul (vonMangoldt_le_nat n) hl (le_max_right _ _) hn₀.le
        _ = y := by field_simp
  have hf : (⌊y⌋₊:ℝ) ≤ y := Nat.floor_le hy₀
  unfold complexPrimeRamp
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ range (⌊y⌋₊+1), y := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg vonMangoldt_nonneg,
        Real.norm_of_nonneg (show 0 ≤ arithmeticRampWeight n y from le_max_right _ _)]
      exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right vonMangoldt_nonneg (ha n)) (le_max_right _ _)).trans (hterm n)
    _ = ((⌊y⌋₊:ℝ)+1)*y := by simp [Nat.cast_add]
    _ ≤ (y+1)*y := mul_le_mul_of_nonneg_right (add_le_add hf le_rfl) hy₀
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hy) hy₀]

private theorem complexPrimeRamp_laplace (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {s : ℂ} (hs : 2 < s.re) :
    (∫ u in Ioi (0:ℝ), complexPrimeRamp a (Real.exp u)*Complex.exp (-s*(u:ℂ))) =
      LSeries (fun n => (vonMangoldt n:ℂ) * a n) s/(s*(s-1)) := by
  have hσ : 1 < s.re := by linarith
  let H (n : ℕ) (u : ℝ) : ℂ := a n*weightedRampTerm n s u
  have hi (n : ℕ) : IntegrableOn (H n) (Ioi (0:ℝ)) :=
    (weightedRampTerm_integrable hσ n).const_mul _
  have hNorm (n : ℕ) : (∫ u in Ioi (0:ℝ), ‖H n u‖) = ‖a n‖ * ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖ := by
    simp only [H,norm_mul,integral_const_mul]
  have hsum : Summable fun n => ∫ u in Ioi (0:ℝ), ‖H n u‖ := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) _
      (summable_weightedRamp_integral_norm hs)
    intro n
    rw [hNorm]
    exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) (ha n)
  have hhs := hasSum_integral_of_summable_integral_norm hi hsum
  have hPoint (u : ℝ) : (∑' n, H n u) =
      complexPrimeRamp a (Real.exp u)*Complex.exp (-s*(u:ℂ)) := by
    rw [tsum_eq_sum (s := range (⌊Real.exp u⌋₊+1)) (by
      intro n hn
      dsimp only [H,weightedRampTerm,rampLaplaceTerm]
      rw [arithmeticRampWeight_zero_off_range hn, Complex.ofReal_zero,zero_mul,mul_zero,mul_zero])]
    simp only [complexPrimeRamp, sum_mul]
    apply sum_congr rfl
    intro n _
    dsimp [H,weightedRampTerm,rampLaplaceTerm]
    ring
  have hTerm (n : ℕ) : (∫ u in Ioi (0:ℝ), H n u) =
      LSeries.term (fun n => (vonMangoldt n:ℂ) * a n) s n/(s*(s-1)) := by
    dsimp [H]
    rw [integral_const_mul, weightedRampTerm_integral hσ]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn]
      ring
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun u _ => hPoint u), ← hhs.tsum_eq]
  simp_rw [hTerm]
  rw [tsum_div_const]
  rfl

private theorem complexPrimeRamp_continuous (a : ℕ → ℂ) : Continuous (complexPrimeRamp a) := by
  rw [continuous_iff_continuousAt]
  intro y
  let K := ⌊y+1⌋₊+1
  let P (z : ℝ) : ℂ := ∑ n ∈ range K, (vonMangoldt n:ℂ) * a n * (arithmeticRampWeight n z:ℂ)
  have hP : Continuous P := continuous_finsetSum _ fun n _ => by unfold arithmeticRampWeight; fun_prop
  apply hP.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (show y < y+1 by linarith)] with z hz
  unfold complexPrimeRamp P
  apply sum_subset (range_mono (Nat.succ_le_succ (Nat.floor_mono (show z ≤ y+1 from hz.le))))
  intro n _ hn
  rw [arithmeticRampWeight_zero_off_range hn,Complex.ofReal_zero,mul_zero]

private theorem complexPrimeRamp_weighted_integrable (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    IntegrableOn (fun u : ℝ => complexPrimeRamp a (Real.exp u)*Complex.exp (-(3:ℂ)*(u:ℂ))) (Ioi 0) := by
  have hf : Continuous (fun u : ℝ => complexPrimeRamp a (Real.exp u)*Complex.exp (-(3:ℂ)*(u:ℂ))) :=
    ((complexPrimeRamp_continuous a).comp Real.continuous_exp).mul (by fun_prop)
  have hin : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    have h := (integrableOn_exp_mul_complex_Ioi (a := (-1:ℂ)) (by norm_num) 0).norm
    change Integrable (fun u : ℝ => Real.exp (-u)) ((volume:Measure ℝ).restrict (Ioi 0))
    simpa [Complex.norm_exp,Complex.mul_re] using h
  apply (hin.const_mul (2:ℝ)).mono' hf.aestronglyMeasurable
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have h := complexPrimeRamp_growth a ha (Real.one_le_exp (show 0 ≤ u from hu.le))
  have h₂ : (Real.exp u)^2 = Real.exp (2*u) := by simpa using (Real.exp_nat_mul u 2).symm
  rw [h₂] at h
  rw [norm_mul,Complex.norm_exp]
  have he : (-(3:ℂ)*(u:ℂ)).re = -3*u := by norm_num [Complex.mul_re]
  rw [he]
  calc
    _ ≤ (2*Real.exp (2*u))*Real.exp (-3*u) := mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2 <;> ring

private theorem norm_dirichlet_logDerivative_le_on_right {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ ∑' n : ℕ,
      ‖LSeries.term (fun n => (vonMangoldt n:ℂ)) (2:ℂ) n‖ := by
  let a : ℕ → ℂ := fun n => χ (n:ZMod q) * (vonMangoldt n:ℂ)
  let b : ℕ → ℂ := fun n => (vonMangoldt n:ℂ)
  have hs1 : 1 < s.re := by linarith
  have hL : LSeries a s = -(deriv χ.LFunction s / χ.LFunction s) := by
    rw [χ.deriv_LFunction_eq_deriv_LSeries hs1, χ.LFunction_eq_LSeries hs1, ← neg_div]
    exact χ.LSeries_twist_vonMangoldt_eq hs1
  have hB : LSeriesSummable b (2:ℂ) := LSeriesSummable_vonMangoldt (by norm_num)
  have hA : LSeriesSummable a s := χ.LSeriesSummable_twist_vonMangoldt hs1
  have hPt (n : ℕ) : ‖LSeries.term a s n‖ ≤ ‖LSeries.term b (2:ℂ) n‖ := by
    by_cases h0 : n = 0
    · simp [h0]
    rw [LSeries.term_of_ne_zero h0,LSeries.term_of_ne_zero h0,norm_div,norm_div,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h0),norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h0)]
    have hn : (1:ℝ) ≤ n := by exact_mod_cast (Nat.pos_of_ne_zero h0)
    refine div_le_div₀ (norm_nonneg _) ?_ (by positivity) ?_
    · simp only [a,b,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    · exact Real.rpow_le_rpow_of_exponent_le hn (by simpa using hs)
  rw [← norm_neg, ← hL]
  exact (norm_tsum_le_tsum_norm hA.norm).trans (hA.norm.tsum_le_tsum hPt hB.norm)

def unweightedRampTransform (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  -logDeriv f s/(s*(s-1))

theorem rampIntegrand_eq {f : ℂ → ℂ} (y : ℝ) (z : ℂ) :
    rampIntegrand f y z = (y:ℂ)^z * unweightedRampTransform f z := by
  dsimp [rampIntegrand,rampWeight,unweightedRampTransform]
  ring

theorem norm_logDeriv_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 2 ≤ z.re → ‖logDeriv χ.LFunction z‖ ≤ M := by
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun j => (vonMangoldt j:ℂ)) (2:ℂ) n‖,
    tsum_nonneg (fun _ => norm_nonneg _),?_⟩
  exact fun z hz => norm_dirichlet_logDerivative_le_on_right χ hz

theorem right_inverse_ramp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {y : ℝ} (hy : 1 < y) (hI : Integrable (fun t : ℝ => unweightedRampTransform χ.LFunction (point 3 t))) :
    (1/(2*(Real.pi:ℂ)))*(∫ t : ℝ, rampIntegrand χ.LFunction y (point 3 t)) =
      complexPrimeRamp (fun n => χ (n:ZMod q)) y := by
  let a : ℕ → ℂ := fun n => χ (n:ZMod q)
  let F := unweightedRampTransform χ.LFunction
  let g (u : ℝ) := complexPrimeRamp a (Real.exp u)
  have hA : ∀ n, ‖a n‖ ≤ 1 := fun n => χ.norm_le_one _
  have hLap (t : ℝ) : F ((3:ℂ)+(t:ℂ)*I) =
      ∫ u in Ioi (0:ℝ), g u*Complex.exp (-((3:ℂ)+(t:ℂ)*I)*(u:ℂ)) := by
    let w := (3:ℂ)+(t:ℂ)*I
    have hw : w.re = 3 := by simp [w]
    have h2 : 2 < w.re := by rw [hw]; norm_num
    have h1 : 1 < w.re := by linarith
    change F w = ∫ u in Ioi (0:ℝ), complexPrimeRamp a (Real.exp u)*Complex.exp (-w*(u:ℂ))
    rw [complexPrimeRamp_laplace a hA h2]
    have hL : LSeries (fun n => (vonMangoldt n:ℂ)*a n) w = -logDeriv χ.LFunction w := by
      simp only [a,mul_comm (vonMangoldt _ : ℂ)]
      rw [logDeriv,Pi.div_apply,χ.deriv_LFunction_eq_deriv_LSeries h1,χ.LFunction_eq_LSeries h1,← neg_div]
      exact χ.LSeries_twist_vonMangoldt_eq h1
    rw [hL]
    rfl
  have hy₀ : 0 < y := zero_lt_one.trans hy
  have hc : ContinuousAt g (Real.log y) :=
    ((complexPrimeRamp_continuous a).comp Real.continuous_exp).continuousAt
  have h := vertical_laplace_inversion g F 3 (complexPrimeRamp_weighted_integrable a hA)
    hLap (by simp only [point_eq] at hI; exact hI) (Real.log y) (Real.log_pos hy) hc
  have hP (t : ℝ) : Complex.exp (point 3 t*(Real.log y:ℂ)) = (y:ℂ)^(point 3 t) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy₀.ne'),← Complex.ofReal_log hy₀.le,mul_comm]
  simp_rw [← point_eq] at h
  change (1/(2*(Real.pi:ℂ)))*(∫ t : ℝ,
    Complex.exp (point 3 t*(Real.log y:ℂ))*F (point 3 t)) =
      complexPrimeRamp a (Real.exp (Real.log y)) at h
  rw [Real.exp_log hy₀] at h
  simp_rw [hP] at h
  simpa only [rampIntegrand_eq] using h

theorem complexPrimeRamp_re (a : ℕ → ℂ) (y : ℝ) :
    (complexPrimeRamp a y).re =
      ∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (a n).re * max (y/(n:ℝ)-1) 0 := by
  simp only [complexPrimeRamp,arithmeticRampWeight,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]

end MasulloDirichletEndpoint

set_option autoImplicit false
set_option maxHeartbeats 2400000

open Complex Set Finset Filter Topology Metric MeasureTheory Asymptotics ArithmeticFunction
open scoped Interval Classical

noncomputable section

namespace MasulloDirichletEndpoint

private theorem halfwidth_norm_le (z : ℂ) (c : ℝ) (_hc : 0 ≤ c) (hc₁ : c ≤ 1)
    (hz : c ≤ |z.re|) : (c/2)*(1+|z.im|) ≤ ‖z‖ := by
  have h1 : c ≤ ‖z‖ := hz.trans (abs_re_le_norm _)
  have h2 : c*|z.im| ≤ ‖z‖ :=
    (mul_le_of_le_one_left (abs_nonneg _) hc₁).trans (abs_im_le_norm _)
  linarith

theorem denominator_lower_of_real_parts (z : ℂ) {c d : ℝ} (hc : 0 ≤ c) (hc₁ : c ≤ 1)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hcZ : c ≤ |z.re|) (hdZ : d ≤ |z.re-1|) :
    (c*d/4)*(1+|z.im|)^2 ≤ ‖z‖*‖z-1‖ := by
  have h1 := halfwidth_norm_le z c hc hc₁ hcZ
  have h2 := halfwidth_norm_le (z-1) d hd hd₁ (by simpa only [sub_re,one_re] using hdZ)
  simp only [sub_im,one_im,sub_zero] at h2
  calc
    _ = ((c/2)*(1+|z.im|))*((d/2)*(1+|z.im|)) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

theorem denominator_lower_high (z : ℂ) (h : 1 ≤ |z.im|) :
    (1/4:ℝ)*(1+|z.im|)^2 ≤ ‖z‖*‖z-1‖ := by
  have h1 : (1+|z.im|)/2 ≤ ‖z‖ := (by linarith : (1+|z.im|)/2 ≤ |z.im|).trans (abs_im_le_norm _)
  have h2 : (1+|z.im|)/2 ≤ ‖z-1‖ := by
    have h' := abs_im_le_norm (z-1)
    simp only [sub_im,one_im,sub_zero] at h'
    exact (by linarith : (1+|z.im|)/2 ≤ |z.im|).trans h'
  calc
    _ = ((1+|z.im|)/2)*((1+|z.im|)/2) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

theorem norm_unweightedRampTransform_le {f : ℂ → ℂ} {z : ℂ} {d : ℝ} (hd : 0 < d)
    (hDen : d*(1+|z.im|)^2 ≤ ‖z‖*‖z-1‖) :
    ‖unweightedRampTransform f z‖ ≤ d⁻¹*weightedLogDeriv f z := by
  have hW : 0 < 1+|z.im| := by positivity
  unfold unweightedRampTransform weightedLogDeriv quadraticWeight
  rw [norm_div,norm_neg,norm_mul]
  calc
    _ ≤ ‖logDeriv f z‖/(d*(1+|z.im|)^2) := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hDen
    _ = _ := by
      rw [show (1+|z.im|)^(-2:ℝ) = ((1+|z.im|)^2)⁻¹ by
        rw [Real.rpow_neg hW.le,Real.rpow_two],div_eq_mul_inv,mul_inv]
      ring

theorem norm_rampIntegrand_le {f : ℂ → ℂ} {z : ℂ} {d y β : ℝ} (hy : 1 ≤ y) (hd : 0 < d)
    (hz : z.re ≤ β) (hDen : d*(1+|z.im|)^2 ≤ ‖z‖*‖z-1‖) :
    ‖rampIntegrand f y z‖ ≤ (d⁻¹*y^β)*weightedLogDeriv f z := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hW : 0 ≤ weightedLogDeriv f z :=
    mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _)
  rw [rampIntegrand_eq,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy₀]
  calc
    _ ≤ y^β*(d⁻¹*weightedLogDeriv f z) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hy hz)
        (norm_unweightedRampTransform_le hd hDen) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_rampResidue_le {f : ℂ → ℂ} {z : ℂ} {d y β : ℝ} (hy : 1 ≤ y) (hd : 0 < d)
    (hz : z.re ≤ β) (hz₁ : z ≠ 1) (hDen : d*(1+|z.im|)^2 ≤ ‖z‖*‖z-1‖) :
    ‖rampResidue f y z‖ ≤ (d⁻¹*y^β)*(multiplicity f z*quadraticWeight z.im) := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hW : 0 < 1+|z.im| := by positivity
  rw [rampResidue,if_neg hz₁,norm_mul,Complex.norm_natCast,rampWeight,
    norm_div,norm_neg,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy₀]
  have h : y^z.re/(‖z‖*‖z-1‖) ≤ y^β/(d*(1+|z.im|)^2) :=
    div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hy hz) (by positivity) hDen
  refine (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq ?_
  unfold multiplicity quadraticWeight
  rw [show (1+|z.im|)^(-2:ℝ) = ((1+|z.im|)^2)⁻¹ by
    rw [Real.rpow_neg hW.le,Real.rpow_two],div_eq_mul_inv,mul_inv]
  ring

private theorem integrable_quadraticWeight : Integrable quadraticWeight := by
  have h := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ))
    (r := 2) (by norm_num)
  change Integrable (fun t : ℝ => quadraticWeight t)
  simpa only [quadraticWeight,Real.norm_eq_abs] using h

theorem integrable_right_unweighted {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    Integrable (fun t : ℝ => unweightedRampTransform χ.LFunction (point 3 t)) := by
  let f := χ.LFunction
  have hD : Differentiable ℂ f := fun z => χ.differentiableAt_LFunction z (.inr hχ)
  obtain ⟨M,hM,hBounds⟩ := norm_logDeriv_right χ
  have hP : Continuous (point 3) := by
    change Continuous (fun t : ℝ => point 3 t)
    simp_rw [point_eq]
    fun_prop
  have h₀ (t : ℝ) : point 3 t ≠ 0 := Complex.ne_zero_of_re_pos (by norm_num)
  have h₁ (t : ℝ) : point 3 t-1 ≠ 0 := Complex.ne_zero_of_re_pos (by norm_num [Complex.sub_re])
  have hL : Continuous (fun t : ℝ => logDeriv f (point 3 t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analytic_logDeriv_at hD (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simp))).continuousAt.comp hP.continuousAt
  have hF : Continuous (fun t : ℝ => unweightedRampTransform f (point 3 t)) :=
    hL.neg.div (hP.mul (hP.sub continuous_const)) (fun t => mul_ne_zero (h₀ t) (h₁ t))
  apply (integrable_quadraticWeight.const_mul (4*M)).mono' hF.aestronglyMeasurable
  refine Eventually.of_forall (fun t => ?_)
  have hDen := denominator_lower_of_real_parts (point 3 t)
    (c := 1) (d := 1) zero_le_one le_rfl zero_le_one le_rfl (by simp) (by simp; norm_num)
  norm_num only [one_mul] at hDen
  refine (norm_unweightedRampTransform_le (by norm_num : 0 < (1/4:ℝ)) hDen).trans ?_
  have h := hBounds (point 3 t) (by norm_num)
  simp only [weightedLogDeriv,point_im]
  norm_num
  nlinarith only [mul_nonneg (quadraticWeight_nonneg t) (sub_nonneg.mpr h)]

private theorem height_tendsto {T : ℕ → ℝ} (hT : ∀ n : ℕ, (n:ℝ)+1 < T n) :
    Tendsto T atTop atTop := by
  refine tendsto_atTop.mpr fun x => ?_
  obtain ⟨n,hn⟩ := exists_nat_gt x
  filter_upwards [eventually_ge_atTop n] with m hm
  have hm' : (n:ℝ) ≤ m := by exact_mod_cast hm
  linarith [hT m]

private theorem contour_limit {f : ℂ → ℂ} {a : ℝ} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hL : Integrable (fun t : ℝ => f (point a t))) (hR : Integrable (fun t : ℝ => f (point 3 t)))
    (hBot : Tendsto (fun n => HIntegral f a 3 (-T n)) atTop (𝓝 0))
    (hTop : Tendsto (fun n => HIntegral f a 3 (T n)) atTop (𝓝 0)) :
    Tendsto (fun n => RectangleIntegral' f (point a (-T n)) (point 3 (T n))) atTop
      (𝓝 ((1/(2*(Real.pi:ℂ)))*((∫ t : ℝ, f (point 3 t))-(∫ t : ℝ, f (point a t))))) := by
  let L := ∫ t : ℝ, f (point a t)
  let R := ∫ t : ℝ, f (point 3 t)
  have hNeg := tendsto_neg_atTop_atBot.comp hT
  have hLV : Tendsto (fun n => VIntegral f a (-T n) (T n)) atTop (𝓝 (I*L)) := by
    have hx := (intervalIntegral_tendsto_integral hL hNeg hT).const_mul I
    simpa only [VIntegral,smul_eq_mul,point_eq,Function.comp_apply,L] using hx
  have hRV : Tendsto (fun n => VIntegral f 3 (-T n) (T n)) atTop (𝓝 (I*R)) := by
    have hx := (intervalIntegral_tendsto_integral hR hNeg hT).const_mul I
    simpa only [VIntegral,smul_eq_mul,point_eq,Function.comp_apply,R] using hx
  have hLim := (((hBot.sub hTop).add hRV).sub hLV).const_mul (1/(2*(Real.pi:ℂ)*I))
  have hI : (1/(2*(Real.pi:ℂ)*I))*(I*R-I*L) = (1/(2*(Real.pi:ℂ)))*(R-L) := by
    field_simp [I_ne_zero]
  simpa only [RectangleIntegral',RectangleIntegral,point_re,point_im,smul_eq_mul,
    zero_sub_zero,zero_add,hI,L,R] using hLim


private theorem measurable_rampIntegrand {f : ℂ → ℂ} (hf : Measurable f) {y : ℝ} (hy : 0 < y) :
    Measurable (rampIntegrand f y) := by
  let : NeZero (y:ℂ) := ⟨by exact_mod_cast hy.ne'⟩
  have hP : Measurable (fun z : ℂ => (y:ℂ)^z) :=
    (differentiable_const_cpow_of_neZero _).continuous.measurable
  have hW : Measurable (rampWeight y) :=
    hP.neg.div (measurable_id.mul (measurable_id.sub_const 1))
  exact hW.mul ((measurable_deriv f).div hf)

private theorem norm_horizontalIntegral_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a t y : ℝ} (ha : 2/3 ≤ a) (ha₃ : a ≤ 3) (ht : 1 ≤ |t|) (hy : 1 ≤ y)
    (hf : ∀ r ∈ Icc (2/3:ℝ) 3, χ.LFunction (point r t) ≠ 0) :
    ‖HIntegral (rampIntegrand χ.LFunction y) a 3 t‖ ≤ (4*y^(3:ℝ))*horizontalMass χ t := by
  let f := χ.LFunction
  have hDiff : Differentiable ℂ f := fun z => χ.differentiableAt_LFunction z (.inr hχ)
  have hC : Continuous (fun r : ℝ => point r t) := by simp_rw [point_eq]; fun_prop
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hIntA : IntegrableOn (fun r : ℝ => rampIntegrand f y (point r t)) (Icc (2/3:ℝ) 3) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro r hr
    have h₀ : point r t ≠ 0 := Complex.ne_zero_of_re_pos (by simp only [point_re]; linarith [hr.1])
    have h₁ : point r t ≠ 1 := by
      intro h
      have he : t = 0 := by simpa only [point_im,one_im] using congrArg Complex.im h
      norm_num [he] at ht
    have hAn := (analytic_rampWeight hy₀ h₀ h₁).mul (analytic_logDeriv_at hDiff (hf r hr))
    have hCont : ContinuousAt (fun x : ℝ => rampIntegrand f y (point x t)) r :=
      hAn.continuousAt.comp (f := fun x : ℝ => point x t) (hC.continuousAt (x := r))
    exact hCont.continuousWithinAt
  have hIntB : IntegrableOn (fun r : ℝ => weightedLogDeriv f (point r t)) (Icc (2/3:ℝ) 3) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro r hr
    have hAn := analytic_logDeriv_at hDiff (hf r hr)
    change ContinuousWithinAt (fun r : ℝ => quadraticWeight t*‖logDeriv f (point r t)‖) _ r
    have hCont : ContinuousAt (fun x : ℝ => logDeriv f (point x t)) r :=
      hAn.continuousAt.comp (f := fun x : ℝ => point x t) (hC.continuousAt (x := r))
    exact (hCont.norm.const_mul _).continuousWithinAt
  have hSub : Ioc a (3:ℝ) ⊆ Icc (2/3:ℝ) 3 := fun r hr => ⟨ha.trans hr.1.le,hr.2⟩
  have hNorm (r : ℝ) (hr : r ∈ Ioc a 3) :
      ‖rampIntegrand f y (point r t)‖ ≤ (4*y^(3:ℝ))*weightedLogDeriv f (point r t) := by
    have h := norm_rampIntegrand_le (f := f) (z := point r t) hy
      (d := 1/4) (by norm_num) (β := 3) (by simpa only [point_re] using hr.2)
      (denominator_lower_high _ (by simpa only [point_im] using ht))
    norm_num at h ⊢
    exact h
  rw [HIntegral,intervalIntegral.integral_of_le ha₃]
  simp_rw [← point_eq]
  change ‖∫ r : ℝ in Ioc a 3,rampIntegrand f y (point r t)‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ r : ℝ in Ioc a 3,(4*y^(3:ℝ))*weightedLogDeriv f (point r t) :=
      integral_mono_ae (hIntA.mono_set hSub).norm ((hIntB.mono_set hSub).const_mul _)
        ((ae_restrict_mem measurableSet_Ioc).mono hNorm)
    _ ≤ _ := by
      rw [integral_const_mul,horizontalMass]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set hIntB
        (Eventually.of_forall fun r => mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _))
        (Eventually.of_forall hSub)

private theorem horizontal_integrals_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a y : ℝ} (ha : 2/3 ≤ a) (ha₃ : a ≤ 3) (hy : 1 ≤ y)
    {T : ℕ → ℝ} (hT : ∀ n : ℕ, (n:ℝ)+1 < T n ∧
      (∀ r ∈ Icc (2/3:ℝ) 3, χ.LFunction (point r (T n)) ≠ 0 ∧ χ.LFunction (point r (-T n)) ≠ 0) ∧
      horizontalMass χ (T n) + horizontalMass χ (-T n) < 1/((n:ℝ)+1)) :
    Tendsto (fun n => HIntegral (rampIntegrand χ.LFunction y) a 3 (-T n)) atTop (𝓝 0) ∧
      Tendsto (fun n => HIntegral (rampIntegrand χ.LFunction y) a 3 (T n)) atTop (𝓝 0) := by
  have hBound : Tendsto (fun n : ℕ => (4*y^(3:ℝ))*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4*y^(3:ℝ)))
  have hH (n : ℕ) : 1 ≤ T n := by linarith [(hT n).1,Nat.cast_nonneg (α := ℝ) n]
  have hP (n : ℕ) : 1 ≤ |T n| := (hH n).trans (le_abs_self _)
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hBound
    refine Eventually.of_forall fun n => ?_
    apply (norm_horizontalIntegral_le χ hχ ha ha₃ (by simpa only [abs_neg] using hP n) hy
      (fun r hr => ((hT n).2.1 r hr).2)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [(hT n).2.2,horizontalMass_nonneg χ (T n)]
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hBound
    refine Eventually.of_forall fun n => ?_
    apply (norm_horizontalIntegral_le χ hχ ha ha₃ (hP n) hy (fun r hr => ((hT n).2.1 r hr).1)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [(hT n).2.2,horizontalMass_nonneg χ (-T n)]

theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℝ) (hβ₀ : 3/4 ≤ β) (hβ₁ : β < 1)
    (hZero : ∀ z : ℂ, χ.LFunction z = 0 → z.re ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 < y →
      |(∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
        y * (deriv χ.LFunction 1 / χ.LFunction 1).re| ≤ C*y^β := by
  let f := χ.LFunction
  have hDiff : Differentiable ℂ f := fun z => χ.differentiableAt_LFunction z (.inr hχ)
  have hMeas : Measurable f := hDiff.continuous.measurable
  obtain ⟨a,ha,hNoLeft,hAreaLeft⟩ := exists_good_vertical_edge χ hχ
  have haβ : a ≤ β := ha.2.le.trans hβ₀
  have ha₁ : a < 1 := lt_of_le_of_lt haβ hβ₁
  have ha₃ : a ≤ 3 := ha₁.le.trans (by norm_num)
  have ha₀ : 0 < a := (by norm_num : (0:ℝ)<2/3).trans ha.1
  obtain ⟨T,hT⟩ := exists_good_horizontal_edges χ hχ
  have hT₀ (n : ℕ) : 0 < T n := by linarith [(hT n).1,Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨M,hM,hMass⟩ := bounded_weighted_zero_sums χ hχ
  let dL := a*(1-a)/4
  let dZ := (2/3:ℝ)*(1-β)/4
  have hdL : 0 < dL := by dsimp [dL]; positivity
  have hdZ : 0 < dZ := by dsimp [dZ]; positivity
  let K := dL⁻¹*(∫ t : ℝ, weightedLogDeriv f (point a t))
  have hK : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hdL.le)
    (integral_nonneg fun _ => mul_nonneg (quadraticWeight_nonneg _) (norm_nonneg _))
  let C := K+dZ⁻¹*M
  have hC : 0 ≤ C := add_nonneg hK (mul_nonneg (inv_nonneg.mpr hdZ.le) hM)
  have hRightU := integrable_right_unweighted χ hχ
  have hCv (r : ℝ) : Continuous (point r) := by
    change Continuous (fun t : ℝ => point r t)
    simp_rw [point_eq]
    fun_prop
  refine ⟨C,hC,fun y hy => ?_⟩
  have hy₀ : 0 < y := zero_lt_one.trans hy
  let F := rampIntegrand f y
  let R := ∫ t : ℝ, F (point 3 t)
  let L := ∫ t : ℝ, F (point a t)
  let c : ℂ := 1/(2*(Real.pi:ℂ))
  have hFc : Measurable F := measurable_rampIntegrand hMeas hy₀
  have hLeftBound (t : ℝ) :
      ‖F (point a t)‖ ≤ (dL⁻¹*y^β)*weightedLogDeriv f (point a t) := by
    apply norm_rampIntegrand_le hy.le hdL (by simpa only [point_re] using haβ)
    apply denominator_lower_of_real_parts _ ha₀.le ha₁.le
      (sub_nonneg.mpr ha₁.le) (by linarith) 
    · simp only [point_re]
      exact le_abs_self _
    · simp only [point_re]
      rw [abs_of_nonpos (sub_nonpos.mpr ha₁.le)]
      ring_nf
      exact le_rfl
  have hLeft : Integrable (fun t : ℝ => F (point a t)) :=
    (hAreaLeft.const_mul _).mono' (hFc.comp (hCv a).measurable).aestronglyMeasurable
      (Eventually.of_forall hLeftBound)
  have hRight : Integrable (fun t : ℝ => F (point 3 t)) := by
    apply (hRightU.norm.const_mul (y^(3:ℝ))).mono' (hFc.comp (hCv 3).measurable).aestronglyMeasurable
    refine Eventually.of_forall fun t => ?_
    change ‖F (point 3 t)‖ ≤ _
    rw [show F (point 3 t) = (y:ℂ)^(point 3 t)*unweightedRampTransform f (point 3 t)
      from rampIntegrand_eq _ _,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy₀,point_re]
  have hL : ‖L‖ ≤ K*y^β := by
    apply (norm_integral_le_integral_norm _).trans
    have h := integral_mono hLeft.norm (hAreaLeft.const_mul (dL⁻¹*y^β)) hLeftBound
    rw [integral_const_mul] at h
    exact h.trans_eq (by dsimp only [K]; ring)
  let S (n : ℕ) := (rectangle_zero_set_finite χ hχ ha.1.le ha₃ (hT₀ n).le).toFinset
  have hS (n : ℕ) : (S n : Set ℂ) =
    {z ∈ Rectangle (point a (-T n)) (point 3 (T n)) | f z = 0} :=
    Set.Finite.coe_toFinset _
  have hs0 (n : ℕ) (z : ℂ) (hz : z ∈ S n) : z ∈ stripZeros f := by
    have h := (show z ∈ {z ∈ Rectangle (point a (-T n)) (point 3 (T n)) | f z = 0} from hS n ▸ hz)
    have hg := (Complex.mem_reProdIm.mp h.1).1
    simp only [point_re,uIcc_of_le ha₃, Set.mem_Icc] at hg
    exact ⟨Complex.mem_reProdIm.mpr ⟨⟨ha.1.le.trans hg.1,hg.2⟩,Set.mem_univ _⟩,h.2⟩
  have hCoeff (n : ℕ) : ‖∑ z ∈ S n,rampResidue f y z‖ ≤ (dZ⁻¹*M)*y^β := by
    have ht (z : ℂ) (hz : z ∈ S n) :
        ‖rampResidue f y z‖ ≤ (dZ⁻¹*y^β)*(multiplicity f z*quadraticWeight z.im) := by
      have hs := hs0 n z hz
      have hZ := hZero z hs.2
      have hRe := (Complex.mem_reProdIm.mp hs.1).1.1
      have hne : z ≠ 1 := by intro he; simp [he] at hZ; linarith
      apply norm_rampResidue_le hy.le hdZ hZ hne
      apply denominator_lower_of_real_parts _ (by norm_num) (by norm_num)
        (sub_nonneg.mpr hβ₁.le) (by linarith)
      · exact hRe.trans (le_abs_self _)
      · rw [abs_of_nonpos (sub_nonpos.mpr (hZ.trans hβ₁.le))]
        linarith
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ z ∈ S n,(dZ⁻¹*y^β)*(multiplicity f z*quadraticWeight z.im) := Finset.sum_le_sum ht
      _ = (dZ⁻¹*y^β)*(∑ z ∈ S n,multiplicity f z*quadraticWeight z.im) := by rw [Finset.mul_sum]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hMass (S n) (hs0 n)) (by positivity)).trans_eq (by ring)
  obtain ⟨hBot,hTop⟩ := horizontal_integrals_tendsto χ hχ ha.1.le ha₃ hy.le hT
  have hLim := contour_limit (height_tendsto fun n => (hT n).1) hLeft hRight hBot hTop
  have hSumLim : Tendsto (fun n => ∑ z ∈ S n,rampResidue f y z) atTop
      (𝓝 (c*(R-L)+(y:ℂ)*logDeriv f 1)) := by
    have h0 := hLim.add_const ((y:ℂ)*logDeriv f 1)
    apply h0.congr
    intro n
    rw [ramp_rectangle_residues χ hχ hy₀ ha.1.le ha₁ (hT₀ n) hNoLeft (hT n).2.1 (S n) (hS n)]
    change -(y:ℂ)*logDeriv f 1+ (∑ z ∈ S n,rampResidue f y z) +(y:ℂ)*logDeriv f 1 = _
    ring
  have hSlim : ‖c*(R-L)+(y:ℂ)*logDeriv f 1‖ ≤ (dZ⁻¹*M)*y^β :=
    le_of_tendsto hSumLim.norm (Eventually.of_forall hCoeff)
  have hcp : ‖c‖ ≤ 1 := by
    dsimp only [c]
    rw [norm_div,norm_one,norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have hLeftL : ‖c*L‖ ≤ K*y^β := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcp).trans hL
  have hInv : c*R = complexPrimeRamp (fun n => χ (n:ZMod q)) y := right_inverse_ramp χ hy hRightU
  have hP : complexPrimeRamp (fun n => χ (n:ZMod q)) y + (y:ℂ)*logDeriv f 1 =
      (c*(R-L)+(y:ℂ)*logDeriv f 1)+c*L := by
    rw [mul_sub,← hInv]
    ring
  have hF : ‖complexPrimeRamp (fun n => χ (n:ZMod q)) y+(y:ℂ)*logDeriv f 1‖ ≤ C*y^β := by
    rw [hP]
    apply (norm_add_le _ _).trans
    exact (add_le_add hSlim hLeftL).trans_eq (by dsimp only [C]; ring)
  have hFinal := (Complex.abs_re_le_norm _).trans hF
  simpa only [Complex.add_re,complexPrimeRamp_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,logDeriv,Pi.div_apply,f] using hFinal

end MasulloDirichletEndpoint
