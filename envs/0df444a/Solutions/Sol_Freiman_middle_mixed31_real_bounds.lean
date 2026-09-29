-- Prove2me | solution 1 for Freiman.middle_mixed31_real_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:52:32.433255+00:00
-- url     : https://prove2.me/submissions/63b8b880-7105-4729-9010-0fc84ed08f2f

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Freiman

private theorem polyP_pos (p s u v : ℝ)
    (hp : (1/4:ℝ) ≤ p) (hs : (1/4:ℝ) ≤ s)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 2) (hu2 : u^2 = 3)
    (hv0 : 4 ≤ v) (hv1 : v ≤ 5) (hv2 : v^2 = 21) :
    0 < (19/5:ℝ)*((1+s+((v-3)/6))*(1+s+((v-3)/2)))*((1+p*((4+u)/13))*(1+p*((9-u)/13)))-((55/100:ℝ)*(1+s*((15+v)/34))*(1+s*((v-3)/2)))*((3+p+((v-3)/6))*(3+p+((v-3)/2))) := by
  have hprod : 0 ≤ u*v := mul_nonneg hu0 (by linarith)
  have hx : 0 ≤ p-(1/4:ℝ) := by linarith
  have hy : 0 ≤ s-(1/4:ℝ) := by linarith
  have hc00 : 0 < ((3177151/1470976:ℝ) + (475/43264:ℝ)*u + (19/2704:ℝ)*(u*v/3) + (18864041/44129280:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have hc01 : 0 < ((-4627027/919360:ℝ) + (19/5408:ℝ)*u + (19/1352:ℝ)*(u*v/3) + (11587339/5516160:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht01 : 0 ≤ ((-4627027/919360:ℝ) + (19/5408:ℝ)*u + (19/1352:ℝ)*(u*v/3) + (11587339/5516160:ℝ)*v) * (p-1/4)^0 * (s-1/4)^1 := by positivity
  have hc02 : 0 < ((1228823/459680:ℝ) + (19/2704:ℝ)*u + (-341/1088:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht02 : 0 ≤ ((1228823/459680:ℝ) + (19/2704:ℝ)*u + (-341/1088:ℝ)*v) * (p-1/4)^0 * (s-1/4)^2 := by positivity
  have hc10 : 0 < ((3353729/919360:ℝ) + (475/5408:ℝ)*u + (19/338:ℝ)*(u*v/3) + (1423067/1838720:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht10 : 0 ≤ ((3353729/919360:ℝ) + (475/5408:ℝ)*u + (19/338:ℝ)*(u*v/3) + (1423067/1838720:ℝ)*v) * (p-1/4)^1 * (s-1/4)^0 := by positivity
  have hc11 : 0 < ((44471/114920:ℝ) + (19/676:ℝ)*u + (19/169:ℝ)*(u*v/3) + (1175587/689520:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht11 : 0 ≤ ((44471/114920:ℝ) + (19/676:ℝ)*u + (19/169:ℝ)*(u*v/3) + (1175587/689520:ℝ)*v) * (p-1/4)^1 * (s-1/4)^1 := by positivity
  have hc12 : 0 < ((211781/57460:ℝ) + (19/338:ℝ)*u + (-209/680:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht12 : 0 ≤ ((211781/57460:ℝ) + (19/338:ℝ)*u + (-209/680:ℝ)*v) * (p-1/4)^1 * (s-1/4)^2 := by positivity
  have hc20 : 0 < ((352627/459680:ℝ) + (475/2704:ℝ)*u + (19/169:ℝ)*(u*v/3) + (154891/919360:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht20 : 0 ≤ ((352627/459680:ℝ) + (475/2704:ℝ)*u + (19/169:ℝ)*(u*v/3) + (154891/919360:ℝ)*v) * (p-1/4)^2 * (s-1/4)^0 := by positivity
  have hc21 : 0 < ((60357/57460:ℝ) + (19/338:ℝ)*u + (38/169:ℝ)*(u*v/3) + (17809/114920:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht21 : 0 ≤ ((60357/57460:ℝ) + (19/338:ℝ)*u + (38/169:ℝ)*(u*v/3) + (17809/114920:ℝ)*v) * (p-1/4)^2 * (s-1/4)^1 := by positivity
  have hc22 : 0 < ((5379/5746:ℝ) + (19/169:ℝ)*u + (-33/340:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht22 : 0 ≤ ((5379/5746:ℝ) + (19/169:ℝ)*u + (-33/340:ℝ)*v) * (p-1/4)^2 * (s-1/4)^2 := by positivity
  have hv3 : v^3 = 21*v := by
    calc
      v^3 = v^2*v := by ring
      _ = 21*v := by rw [hv2]
  have hv4 : v^4 = (441:ℝ) := by
    calc
      v^4 = (v^2)^2 := by ring
      _ = 441 := by rw [hv2]; norm_num
  have hid : (19/5:ℝ)*((1+s+((v-3)/6))*(1+s+((v-3)/2)))*((1+p*((4+u)/13))*(1+p*((9-u)/13)))-((55/100:ℝ)*(1+s*((15+v)/34))*(1+s*((v-3)/2)))*((3+p+((v-3)/6))*(3+p+((v-3)/2))) =
      ((3177151/1470976:ℝ) + (475/43264:ℝ)*u + (19/2704:ℝ)*(u*v/3) + (18864041/44129280:ℝ)*v) * (p-1/4)^0 * (s-1/4)^0 + ((-4627027/919360:ℝ) + (19/5408:ℝ)*u + (19/1352:ℝ)*(u*v/3) + (11587339/5516160:ℝ)*v) * (p-1/4)^0 * (s-1/4)^1 + ((1228823/459680:ℝ) + (19/2704:ℝ)*u + (-341/1088:ℝ)*v) * (p-1/4)^0 * (s-1/4)^2 + ((3353729/919360:ℝ) + (475/5408:ℝ)*u + (19/338:ℝ)*(u*v/3) + (1423067/1838720:ℝ)*v) * (p-1/4)^1 * (s-1/4)^0 + ((44471/114920:ℝ) + (19/676:ℝ)*u + (19/169:ℝ)*(u*v/3) + (1175587/689520:ℝ)*v) * (p-1/4)^1 * (s-1/4)^1 + ((211781/57460:ℝ) + (19/338:ℝ)*u + (-209/680:ℝ)*v) * (p-1/4)^1 * (s-1/4)^2 + ((352627/459680:ℝ) + (475/2704:ℝ)*u + (19/169:ℝ)*(u*v/3) + (154891/919360:ℝ)*v) * (p-1/4)^2 * (s-1/4)^0 + ((60357/57460:ℝ) + (19/338:ℝ)*u + (38/169:ℝ)*(u*v/3) + (17809/114920:ℝ)*v) * (p-1/4)^2 * (s-1/4)^1 + ((5379/5746:ℝ) + (19/169:ℝ)*u + (-33/340:ℝ)*v) * (p-1/4)^2 * (s-1/4)^2 := by
    ring_nf
    simp only [hu2, hv2, hv3, hv4]
    ring
  rw [hid]
  positivity

private theorem polyQ_pos (p s u v : ℝ)
    (hp : (1/4:ℝ) ≤ p) (hs : (1/4:ℝ) ≤ s)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 2) (hu2 : u^2 = 3)
    (hv0 : 4 ≤ v) (hv1 : v ≤ 5) (hv2 : v^2 = 21) :
    0 < ((328/1000:ℝ)*(1+s*((4+u)/13))*(1+s*((9-u)/13)))*((3+p+((v-3)/6))*(3+p+((v-3)/2)))-(5/19:ℝ)*((1+s+((v-3)/6))*(1+s+((v-3)/2)))*((1+p*((27+v)/118))*(1+p*((15-v)/34))) := by
  have hprod : 0 ≤ u*v := mul_nonneg hu0 (by linarith)
  have hx : 0 ≤ p-(1/4:ℝ) := by linarith
  have hy : 0 ≤ s-(1/4:ℝ) := by linarith
  have hc00 : 0 < ((46260958801/20612051200:ℝ) + (861/216320:ℝ)*u + (41/13520:ℝ)*(u*v/3) + (36439875521/61836153600:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have hc01 : 0 < ((5741031067/2576506400:ℝ) + (861/27040:ℝ)*u + (41/1690:ℝ)*(u*v/3) + (3052226057/7729519200:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht01 : 0 ≤ ((5741031067/2576506400:ℝ) + (861/27040:ℝ)*u + (41/1690:ℝ)*(u*v/3) + (3052226057/7729519200:ℝ)*v) * (p-1/4)^0 * (s-1/4)^1 := by positivity
  have hc02 : 0 < ((143640541/1288253200:ℝ) + (861/13520:ℝ)*u + (41/845:ℝ)*(u*v/3) + (139353187/1288253200:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht02 : 0 ≤ ((143640541/1288253200:ℝ) + (861/13520:ℝ)*u + (41/845:ℝ)*(u*v/3) + (139353187/1288253200:ℝ)*v) * (p-1/4)^0 * (s-1/4)^2 := by positivity
  have hc10 : 0 < ((20730178629/12882532000:ℝ) + (369/135200:ℝ)*u + (41/33800:ℝ)*(u*v/3) + (452089321/2034084000:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht10 : 0 ≤ ((20730178629/12882532000:ℝ) + (369/135200:ℝ)*u + (41/33800:ℝ)*(u*v/3) + (452089321/2034084000:ℝ)*v) * (p-1/4)^1 * (s-1/4)^0 := by positivity
  have hc11 : 0 < ((2589871743/1610316500:ℝ) + (369/16900:ℝ)*u + (41/4225:ℝ)*(u*v/3) + (565363483/4830949500:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht11 : 0 ≤ ((2589871743/1610316500:ℝ) + (369/16900:ℝ)*u + (41/4225:ℝ)*(u*v/3) + (565363483/4830949500:ℝ)*v) * (p-1/4)^1 * (s-1/4)^1 := by positivity
  have hc12 : 0 < ((79957089/805158250:ℝ) + (369/8450:ℝ)*u + (82/4225:ℝ)*(u*v/3) + (39131953/805158250:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht12 : 0 ≤ ((79957089/805158250:ℝ) + (369/8450:ℝ)*u + (82/4225:ℝ)*(u*v/3) + (39131953/805158250:ℝ)*v) * (p-1/4)^1 * (s-1/4)^2 := by positivity
  have hc20 : 0 < ((2448693181/6441266000:ℝ) + (41/67600:ℝ)*u + (-115/16048:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht20 : 0 ≤ ((2448693181/6441266000:ℝ) + (41/67600:ℝ)*u + (-115/16048:ℝ)*v) * (p-1/4)^2 * (s-1/4)^0 := by positivity
  have hc21 : 0 < ((288608527/805158250:ℝ) + (41/8450:ℝ)*u + (-625/38114:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht21 : 0 ≤ ((288608527/805158250:ℝ) + (41/8450:ℝ)*u + (-625/38114:ℝ)*v) * (p-1/4)^2 * (s-1/4)^1 := by positivity
  have hc22 : 0 < ((15644121/402579125:ℝ) + (41/4225:ℝ)*u + (15/19057:ℝ)*v)  := by linarith only [hu0, hv0, hv1, hprod]
  have ht22 : 0 ≤ ((15644121/402579125:ℝ) + (41/4225:ℝ)*u + (15/19057:ℝ)*v) * (p-1/4)^2 * (s-1/4)^2 := by positivity
  have hv3 : v^3 = 21*v := by
    calc
      v^3 = v^2*v := by ring
      _ = 21*v := by rw [hv2]
  have hv4 : v^4 = (441:ℝ) := by
    calc
      v^4 = (v^2)^2 := by ring
      _ = 441 := by rw [hv2]; norm_num
  have hid : ((328/1000:ℝ)*(1+s*((4+u)/13))*(1+s*((9-u)/13)))*((3+p+((v-3)/6))*(3+p+((v-3)/2)))-(5/19:ℝ)*((1+s+((v-3)/6))*(1+s+((v-3)/2)))*((1+p*((27+v)/118))*(1+p*((15-v)/34))) =
      ((46260958801/20612051200:ℝ) + (861/216320:ℝ)*u + (41/13520:ℝ)*(u*v/3) + (36439875521/61836153600:ℝ)*v) * (p-1/4)^0 * (s-1/4)^0 + ((5741031067/2576506400:ℝ) + (861/27040:ℝ)*u + (41/1690:ℝ)*(u*v/3) + (3052226057/7729519200:ℝ)*v) * (p-1/4)^0 * (s-1/4)^1 + ((143640541/1288253200:ℝ) + (861/13520:ℝ)*u + (41/845:ℝ)*(u*v/3) + (139353187/1288253200:ℝ)*v) * (p-1/4)^0 * (s-1/4)^2 + ((20730178629/12882532000:ℝ) + (369/135200:ℝ)*u + (41/33800:ℝ)*(u*v/3) + (452089321/2034084000:ℝ)*v) * (p-1/4)^1 * (s-1/4)^0 + ((2589871743/1610316500:ℝ) + (369/16900:ℝ)*u + (41/4225:ℝ)*(u*v/3) + (565363483/4830949500:ℝ)*v) * (p-1/4)^1 * (s-1/4)^1 + ((79957089/805158250:ℝ) + (369/8450:ℝ)*u + (82/4225:ℝ)*(u*v/3) + (39131953/805158250:ℝ)*v) * (p-1/4)^1 * (s-1/4)^2 + ((2448693181/6441266000:ℝ) + (41/67600:ℝ)*u + (-115/16048:ℝ)*v) * (p-1/4)^2 * (s-1/4)^0 + ((288608527/805158250:ℝ) + (41/8450:ℝ)*u + (-625/38114:ℝ)*v) * (p-1/4)^2 * (s-1/4)^1 + ((15644121/402579125:ℝ) + (41/4225:ℝ)*u + (15/19057:ℝ)*v) * (p-1/4)^2 * (s-1/4)^2 := by
    ring_nf
    simp only [hu2, hv2, hv3, hv4]
    ring
  rw [hid]
  positivity


private theorem tails :
    prefixEval [2,3] middleRho = (4+Real.sqrt 3)/13 ∧
    prefixEval [1,1,3] middleRho = (9-Real.sqrt 3)/13 ∧
    prefixEval [1,1,2] middleBeta = (15+Real.sqrt 21)/34 ∧
    prefixEval [3,1,2] middleBeta = (27+Real.sqrt 21)/118 ∧
    prefixEval [3] middleAlpha = (15-Real.sqrt 21)/34 := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have h3n := Real.sqrt_nonneg (3:ℝ)
  have h21n := Real.sqrt_nonneg (21:ℝ)
  have h3minus : 0 < Real.sqrt 3 - 1 := by nlinarith
  have h21minus : 0 < Real.sqrt 21 - 3 := by nlinarith
  norm_num [prefixEval, middleRho, middleBeta, middleAlpha]
  repeat' constructor
  all_goals field_simp (disch := positivity)
  all_goals nlinarith

theorem solution :
    ∀ p s : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) →
      middleScalarA p s (55/100) < (19/5:ℝ)*middleMixedK p s ∧
      (5/19:ℝ)*middleMixedK p s < middleScalarB p s (328/1000) := by
  intro p s hp hs
  have hu0 := Real.sqrt_nonneg (3:ℝ)
  have hu2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hu1 : Real.sqrt 3 ≤ 2 := by nlinarith
  have hv2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hvn := Real.sqrt_nonneg (21:ℝ)
  have hv0 : 4 ≤ Real.sqrt 21 := by nlinarith
  have hv1 : Real.sqrt 21 ≤ 5 := by nlinarith
  have pp : 0 < p := by linarith [hp.1]
  have sp : 0 < s := by linarith [hs.1]
  have alpha_pos : 0 < (Real.sqrt 21 - 3)/6 := by linarith
  have beta_pos : 0 < (Real.sqrt 21 - 3)/2 := by linarith
  have x2_pos : 0 < (9-Real.sqrt 3)/13 := by linarith
  have z2_pos : 0 < (15-Real.sqrt 21)/34 := by linarith
  have hAd : 0 < (1+p*((4+Real.sqrt 3)/13))*(1+p*((9-Real.sqrt 3)/13)) := by positivity
  have hBd : 0 < (1+p*((27+Real.sqrt 21)/118))*(1+p*((15-Real.sqrt 21)/34)) := by positivity
  have hKd : 0 < (3+p+(Real.sqrt 21-3)/6)*(3+p+(Real.sqrt 21-3)/2) := by positivity
  have hP := polyP_pos p s (Real.sqrt 3) (Real.sqrt 21) hp.1 hs.1 hu0 hu1 hu2 hv0 hv1 hv2
  have hQ := polyQ_pos p s (Real.sqrt 3) (Real.sqrt 21) hp.1 hs.1 hu0 hu1 hu2 hv0 hv1 hv2
  rcases tails with ⟨t1,t2,t3,t4,t5⟩
  unfold middleScalarA middleScalarB middleScalarThreshold middleMixedK
  rw [t1,t2,t3,t4,t5]
  simp only [middleAlpha, middleBeta]
  rw [← mul_div_assoc (19/5:ℝ), ← mul_div_assoc (5/19:ℝ)]
  constructor
  · apply (div_lt_div_iff₀ hAd hKd).mpr
    linarith only [hP]
  · apply (div_lt_div_iff₀ hKd hBd).mpr
    linarith only [hQ]

#print axioms solution
