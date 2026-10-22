-- Prove2me | solution 1 for BirkhoffGlobalSection.standard_hopf_elliptic_rational_disk
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:59:13.603715+00:00
-- url     : https://prove2.me/submissions/6d815d63-5484-4982-bdf8-f9f09b1448cf

import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
import Mathlib.Tactic

open BirkhoffGlobalSection
open scoped ContDiff

private noncomputable def diskScale (u : Plane) : ℝ :=
  2 / (1 + planeNormSq u)

private noncomputable def standardDisk (u : Plane) : Phase :=
  ![diskScale u * u 0, diskScale u - 1, -(diskScale u * u 1), 0]

private theorem denominator_pos (u : Plane) : 0 < 1 + planeNormSq u := by
  dsimp [planeNormSq]
  positivity

private theorem scale_pos (u : Plane) : 0 < diskScale u :=
  div_pos (by norm_num) (denominator_pos u)

private theorem scale_smooth : ContDiff ℝ ∞ diskScale := by
  unfold diskScale planeNormSq
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro u
    exact ne_of_gt (denominator_pos u)

private theorem disk_smooth : ContDiff ℝ ∞ standardDisk := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact scale_smooth.mul (contDiff_apply ℝ ℝ 0)
  · exact scale_smooth.sub contDiff_const
  · exact (scale_smooth.mul (contDiff_apply ℝ ℝ 1)).neg
  · exact contDiff_const

private noncomputable def diskDerivative (u : Plane) : Plane →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![
    diskScale u • ContinuousLinearMap.proj 0 + u 0 • fderiv ℝ diskScale u,
    fderiv ℝ diskScale u,
    -(diskScale u • ContinuousLinearMap.proj 1 + u 1 • fderiv ℝ diskScale u),
    0]

private theorem disk_hasFDeriv (u : Plane) :
    HasFDerivAt standardDisk (diskDerivative u) u := by
  have hs := (scale_smooth.differentiable (by simp) u).hasFDerivAt
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hs.mul (hasFDerivAt_apply 0 u)
  · exact hs.sub_const 1
  · exact (hs.mul (hasFDerivAt_apply 1 u)).neg
  · exact hasFDerivAt_const (0 : ℝ) u

private theorem disk_contact (u v : Plane) :
    phaseRadialContact (standardDisk u) (fderiv ℝ standardDisk u v) =
      (diskScale u) ^ 2 / 2 * (u 0 * v 1 - u 1 * v 0) := by
  rw [(disk_hasFDeriv u).fderiv]
  simp [standardDisk, diskDerivative, phaseRadialContact, phaseSymplecticForm]
  ring

private theorem disk_characteristic (u : Plane) :
    diskCharacteristic standardDisk u = ((diskScale u) ^ 2 / 2) • u := by
  ext i
  fin_cases i <;>
    simp [diskCharacteristic, disk_contact, planeCoordinateVector]

private theorem disk_boundary (u : Plane) (hu : u ∈ unitCircle) :
    standardDisk u = standardHopfCircle u := by
  have hq : planeNormSq u = 1 := hu
  norm_num [standardDisk, diskScale, hq, standardHopfCircle]

private theorem scale_ge_one (u : Plane) (hu : u ∈ closedUnitDisk) :
    1 ≤ diskScale u := by
  apply (le_div_iff₀ (denominator_pos u)).2
  have hq : planeNormSq u ≤ 1 := hu
  linarith

private theorem circle_of_scale_one (u : Plane) (hu : diskScale u = 1) :
    u ∈ unitCircle := by
  have h := (div_eq_iff (ne_of_gt (denominator_pos u))).mp hu
  change planeNormSq u = 1
  linarith

theorem solution :
    Nonempty (PositiveEllipticRationalDisk (standardHopfCircle '' unitCircle)) := by
  refine ⟨{
    disk := standardDisk
    sphere := ?_
    smooth := ?_
    injective := ?_
    immersion := ?_
    boundary := ?_
    antipodal_fibers := ?_
    positive_boundary := ?_
    characteristic_zero := ?_
    elliptic := ?_
  }⟩
  · intro u hu
    have hd := ne_of_gt (denominator_pos u)
    change zNormSq (standardDisk u) + wNormSq (standardDisk u) = 1
    simp [standardDisk, diskScale, zNormSq, wNormSq]
    dsimp [planeNormSq] at *
    field_simp
    <;> nlinarith
  · intro u hu
    exact disk_smooth.contDiffAt
  · intro u hu v hv huv
    have h0 := congrFun huv (0 : Fin 4)
    have h1 := congrFun huv (1 : Fin 4)
    have h2 := congrFun huv (2 : Fin 4)
    simp only [standardDisk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h0 h1 h2
    have hs : diskScale u = diskScale v := by linarith
    have hp := scale_pos u
    rw [← hs] at h0 h2
    have hu0 : u 0 = v 0 := mul_left_cancel₀ (ne_of_gt hp) h0
    have hu1 : u 1 = v 1 := mul_left_cancel₀ (ne_of_gt hp) (neg_injective h2)
    ext i
    fin_cases i
    · exact hu0
    · exact hu1
  · intro u hu v w hvw
    rw [(disk_hasFDeriv u).fderiv] at hvw
    have h0 := congrFun hvw (0 : Fin 4)
    have h1 := congrFun hvw (1 : Fin 4)
    have h2 := congrFun hvw (2 : Fin 4)
    simp [diskDerivative] at h0 h1 h2
    have hp := scale_pos u
    rw [h1] at h0 h2
    have hv0 : diskScale u * v 0 = diskScale u * w 0 := by linarith
    have hv1 : diskScale u * v 1 = diskScale u * w 1 := by linarith
    ext i
    fin_cases i
    · exact mul_left_cancel₀ (ne_of_gt hp) hv0
    · exact mul_left_cancel₀ (ne_of_gt hp) hv1
  · apply Set.image_congr
    intro u hu
    exact disk_boundary u hu
  · intro u hu v hv
    constructor
    · intro heq
      have h1 := congrFun heq (1 : Fin 4)
      simp [standardDisk] at h1
      have hsu := scale_ge_one u hu
      have hsv := scale_ge_one v hv
      have huc := circle_of_scale_one u (by linarith)
      have hvc := circle_of_scale_one v (by linarith)
      refine ⟨huc, hvc, ?_⟩
      rw [disk_boundary u huc, disk_boundary v hvc] at heq
      have h0 := congrFun heq (0 : Fin 4)
      have h2 := congrFun heq (2 : Fin 4)
      ext i
      fin_cases i <;> simp_all [standardHopfCircle] <;> linarith
    · rintro ⟨huc, hvc, rfl⟩
      rw [disk_boundary u huc, disk_boundary (-u) hvc]
      ext i
      fin_cases i <;> simp [standardHopfCircle]
  · intro u hu
    rw [disk_contact]
    have hq : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
    have hs : diskScale u = 1 := by
      norm_num [diskScale, show planeNormSq u = 1 from hu]
    simp [hs, circleTangent]
    nlinarith
  · intro u hu
    rw [disk_characteristic]
    have hs := scale_pos u
    have hp : 0 < (diskScale u) ^ 2 / 2 := by positivity
    exact smul_eq_zero_iff_right (ne_of_gt hp)
  · refine ⟨2, by norm_num, ?_⟩
    have heq : diskCharacteristic standardDisk =
        fun u : Plane => ((diskScale u) ^ 2 / 2) • u := by
      funext u
      exact disk_characteristic u
    rw [heq]
    have hc : DifferentiableAt ℝ (fun u : Plane => (diskScale u) ^ 2 / 2) 0 := by
      exact ((scale_smooth.pow 2).div_const 2).differentiable (by simp) 0
    have hd := hc.hasFDerivAt.smul (hasFDerivAt_id (0 : Plane))
    intro v
    change (fderiv ℝ ((fun u : Plane => (diskScale u) ^ 2 / 2) •
      (id : Plane → Plane)) 0) v = (2 : ℝ) • v
    rw [hd.fderiv]
    norm_num [diskScale, planeNormSq]
