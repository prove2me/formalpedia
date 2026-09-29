-- Prove2me | solution 1 for Erdos9796Mission.three_triad_collision
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T23:20:43.517005+00:00
-- url     : https://prove2.me/submissions/7b1aec89-0231-4194-93da-cd70962f8cea

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry

namespace Erdos9796Mission

private noncomputable def pt (x y : ℝ) : Plane := !₂[x, y]

private noncomputable def normSim (p₁ p₂ x : Plane) : Plane :=
  pt (((x 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (x 1 - p₁ 1) * (p₂ 1 - p₁ 1)) /
      ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2))
    (((x 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (x 0 - p₁ 0) * (p₂ 1 - p₁ 1)) /
      ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2))

private theorem dist_sq_coord (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private theorem normSim_den_pos {p₁ p₂ : Plane} (hp : p₁ ≠ p₂) :
    0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
  have hd : 0 < dist p₁ p₂ := dist_pos.mpr hp
  have hsq : dist p₁ p₂ ^ 2 = (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
    rw [dist_sq_coord]
    ring
  nlinarith [hsq, hd]

private theorem normSim_dist_image (p₁ p₂ : Plane) (hp : p₁ ≠ p₂) (a b : Plane) :
    dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) = (dist p₁ p₂)⁻¹ * dist a b := by
  have hden : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 :=
    ne_of_gt (normSim_den_pos hp)
  have hD : 0 < dist p₁ p₂ := dist_pos.mpr hp
  have hX : 0 ≤ dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) := dist_nonneg
  have h2 : 0 ≤ (dist p₁ p₂)⁻¹ * dist a b :=
    mul_nonneg (inv_nonneg.mpr hD.le) dist_nonneg
  have hkey : dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) ^ 2 * dist p₁ p₂ ^ 2
      = dist a b ^ 2 := by
    rw [dist_sq_coord, dist_sq_coord, dist_sq_coord]
    simp only [normSim, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hsq : dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) ^ 2
      = ((dist p₁ p₂)⁻¹ * dist a b) ^ 2 := by
    rw [mul_pow, inv_pow]
    field_simp
    linear_combination hkey
  rw [← Real.sqrt_sq hX, hsq, Real.sqrt_sq h2]

private theorem normSim_fst (p₁ p₂ : Plane) : normSim p₁ p₂ p₁ = pt 0 0 := by
  simp only [normSim, pt, sub_self, zero_mul, add_zero, zero_div]

private theorem normSim_snd (p₁ p₂ : Plane) (hp : p₁ ≠ p₂) :
    normSim p₁ p₂ p₂ = pt 1 0 := by
  have hden : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 :=
    ne_of_gt (normSim_den_pos hp)
  have e1 : ((p₂ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₂ 1 - p₁ 1) * (p₂ 1 - p₁ 1)) /
      ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = 1 := by
    rw [div_eq_iff hden]
    ring
  have e2 : ((p₂ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₂ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) /
      ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = 0 := by
    rw [div_eq_iff hden]
    ring
  rw [normSim, e1, e2]

private theorem scalar_incompatible
    {x y c e : ℝ} (hy : y ≠ 0)
    (hcircle : x ^ 2 + y ^ 2 = 2 * x)
    (hcenter : e ^ 2 - 2 * c * e = 1 / 4)
    (hEB : x = 2 * e * y)
    (hBC : x = 2 * c * y - c ^ 2 + 3 / 4) : False := by
  have hcircle' := hcircle
  rw [hEB] at hcircle'
  have hfactor : y * ((4 * e ^ 2 + 1) * y - 4 * e) = 0 := by
    nlinarith [hcircle']
  have hlinear : (4 * e ^ 2 + 1) * y - 4 * e = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hy
  have he : e ≠ 0 := by
    intro he
    apply hy
    rw [he] at hlinear
    norm_num at hlinear ⊢
    exact hlinear
  have hcenter' : 8 * e * (e - c) = 4 * e ^ 2 + 1 := by
    nlinarith [hcenter]
  have hmul : 8 * e * (e - c) * y = 4 * e := by
    calc
      8 * e * (e - c) * y = (4 * e ^ 2 + 1) * y := by rw [hcenter']
      _ = 4 * e := by linarith [hlinear]
  have hzero : (4 * e) * (2 * (e - c) * y - 1) = 0 := by
    nlinarith [hmul]
  have hfour_e : 4 * e ≠ 0 := mul_ne_zero (by norm_num) he
  have htwo : 2 * (e - c) * y = 1 := by
    have := (mul_eq_zero.mp hzero).resolve_left hfour_e
    linarith
  have hdiff : 2 * (e - c) * y = 3 / 4 - c ^ 2 := by
    nlinarith [hEB, hBC]
  nlinarith [sq_nonneg c]

set_option maxHeartbeats 2000000 in
private theorem normalized_incompatible
    {B C E : Plane} (hB0 : B ≠ pt 0 0)
    (hBC_BD : dist B C = dist B (pt 1 0))
    (hBD_DA : dist B (pt 1 0) = dist (pt 1 0) (pt 0 0))
    (hCA_CD : dist C (pt 0 0) = dist C (pt 1 0))
    (hCD_CE : dist C (pt 1 0) = dist C E)
    (hEA_EB : dist E (pt 0 0) = dist E B)
    (hEB_ED : dist E B = dist E (pt 1 0)) : False := by
  have hCsq : dist C (pt 0 0) ^ 2 = dist C (pt 1 0) ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hCA_CD
  rw [dist_sq_coord, dist_sq_coord] at hCsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hCsq
  have hC0 : C 0 = 1 / 2 := by nlinarith [hCsq]
  have hEA_ED : dist E (pt 0 0) = dist E (pt 1 0) := hEA_EB.trans hEB_ED
  have hEsq : dist E (pt 0 0) ^ 2 = dist E (pt 1 0) ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hEA_ED
  rw [dist_sq_coord, dist_sq_coord] at hEsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hEsq
  have hE0 : E 0 = 1 / 2 := by nlinarith [hEsq]
  set x := B 0
  set y := B 1
  set c := C 1
  set e := E 1
  have hBDsq : dist B (pt 1 0) ^ 2 = dist (pt 1 0) (pt 0 0) ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hBD_DA
  rw [dist_sq_coord, dist_sq_coord] at hBDsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hBDsq
  have hcircle : x ^ 2 + y ^ 2 = 2 * x := by
    dsimp [x, y]
    nlinarith [hBDsq]
  have hCA_CE : dist C (pt 0 0) = dist C E := hCA_CD.trans hCD_CE
  have hCEsq : dist C (pt 0 0) ^ 2 = dist C E ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hCA_CE
  rw [dist_sq_coord, dist_sq_coord] at hCEsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hCEsq
  have hcenter : e ^ 2 - 2 * c * e = 1 / 4 := by
    dsimp [c, e]
    rw [hC0, hE0] at hCEsq
    nlinarith [hCEsq]
  have hEBsq : dist E (pt 0 0) ^ 2 = dist E B ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hEA_EB
  rw [dist_sq_coord, dist_sq_coord] at hEBsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hEBsq
  rw [hE0] at hEBsq
  have hcircle_coords : (B 0) ^ 2 + (B 1) ^ 2 = 2 * B 0 := by
    simpa [x, y] using hcircle
  have hEB : x = 2 * e * y := by
    dsimp [x, y, e]
    nlinarith [hEBsq, hcircle_coords]
  have hBCsq : dist B C ^ 2 = dist B (pt 1 0) ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) hBC_BD
  rw [dist_sq_coord, dist_sq_coord] at hBCsq
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at hBCsq
  rw [hC0] at hBCsq
  have hBC : x = 2 * c * y - c ^ 2 + 3 / 4 := by
    dsimp [x, y, c]
    nlinarith [hBCsq]
  have hy : y ≠ 0 := by
    intro hy
    have hx : x = 0 := by nlinarith [hEB]
    apply hB0
    ext i
    fin_cases i
    · simpa [x, pt] using hx
    · simpa [y, pt] using hy
  exact scalar_incompatible hy hcircle hcenter hEB hBC

private theorem three_triad_collision_proof
    {A B C D E : Plane}
    (hBC_BD : dist B C = dist B D)
    (hBD_DA : dist B D = dist D A)
    (hCA_CD : dist C A = dist C D)
    (hCD_CE : dist C D = dist C E)
    (hEA_EB : dist E A = dist E B)
    (hEB_ED : dist E B = dist E D) : A = B := by
  by_contra hAB
  have hAD : A ≠ D := by
    intro hAD
    have hBD0 : dist B D = 0 := by rw [hBD_DA, hAD, dist_self]
    have hBD : B = D := dist_eq_zero.mp hBD0
    exact hAB (hAD.trans hBD.symm)
  let T : Plane → Plane := normSim A D
  let b := T B
  let c := T C
  let e := T E
  have hdist (X Y : Plane) :
      dist (T X) (T Y) = (dist A D)⁻¹ * dist X Y := by
    simpa [T] using normSim_dist_image A D hAD X Y
  have hT0 : T A = pt 0 0 := by simpa [T] using normSim_fst A D
  have hT1 : T D = pt 1 0 := by simpa [T] using normSim_snd A D hAD
  have hTinj : Function.Injective T := by
    intro X Y hXY
    have hzero : dist (T X) (T Y) = 0 := by rw [hXY, dist_self]
    rw [hdist] at hzero
    have hscale : (dist A D)⁻¹ ≠ 0 := inv_ne_zero (dist_ne_zero.mpr hAD)
    exact dist_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hscale)
  have hb0 : b ≠ pt 0 0 := by
    intro hb0
    apply hAB
    apply hTinj
    simpa [b, hT0] using hb0.symm
  apply normalized_incompatible hb0
  · calc
      dist b c = (dist A D)⁻¹ * dist B C := by simpa [b, c] using hdist B C
      _ = (dist A D)⁻¹ * dist B D := by rw [hBC_BD]
      _ = dist b (pt 1 0) := by rw [← hT1]; simpa [b] using (hdist B D).symm
  · calc
      dist b (pt 1 0) = dist (T B) (T D) := by simp [b, hT1]
      _ = (dist A D)⁻¹ * dist B D := hdist B D
      _ = (dist A D)⁻¹ * dist D A := by rw [hBD_DA]
      _ = dist (T D) (T A) := (hdist D A).symm
      _ = dist (pt 1 0) (pt 0 0) := by rw [hT0, hT1]
  · calc
      dist c (pt 0 0) = dist (T C) (T A) := by simp [c, hT0]
      _ = (dist A D)⁻¹ * dist C A := hdist C A
      _ = (dist A D)⁻¹ * dist C D := by rw [hCA_CD]
      _ = dist (T C) (T D) := (hdist C D).symm
      _ = dist c (pt 1 0) := by simp [c, hT1]
  · calc
      dist c (pt 1 0) = dist (T C) (T D) := by simp [c, hT1]
      _ = (dist A D)⁻¹ * dist C D := hdist C D
      _ = (dist A D)⁻¹ * dist C E := by rw [hCD_CE]
      _ = dist c e := by simpa [c, e] using (hdist C E).symm
  · calc
      dist e (pt 0 0) = dist (T E) (T A) := by simp [e, hT0]
      _ = (dist A D)⁻¹ * dist E A := hdist E A
      _ = (dist A D)⁻¹ * dist E B := by rw [hEA_EB]
      _ = dist e b := by simpa [e, b] using (hdist E B).symm
  · calc
      dist e b = (dist A D)⁻¹ * dist E B := by simpa [e, b] using hdist E B
      _ = (dist A D)⁻¹ * dist E D := by rw [hEB_ED]
      _ = dist e (pt 1 0) := by rw [← hT1]; simpa [e] using (hdist E D).symm

end Erdos9796Mission

open Erdos9796Mission

theorem solution
    {A B C D E : Plane}
    (hBC_BD : dist B C = dist B D)
    (hBD_DA : dist B D = dist D A)
    (hCA_CD : dist C A = dist C D)
    (hCD_CE : dist C D = dist C E)
    (hEA_EB : dist E A = dist E B)
    (hEB_ED : dist E B = dist E D) : A = B := by
  exact Erdos9796Mission.three_triad_collision_proof
    hBC_BD hBD_DA hCA_CD hCD_CE hEA_EB hEB_ED
