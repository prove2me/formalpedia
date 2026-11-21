-- Prove2me | solution 1 for Erdos324.linear_quartic_cube_class_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T19:49:59.2679+00:00
-- url     : https://prove2.me/submissions/7da36334-4658-4595-9082-3ef0cfac07ed

import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

Matt directed the investigation. OpenAI Codex (Astra) developed the construction
and Lean formalization. The arithmetic-progression construction starts from
John Leech's 1957 equal-fourth-powers identity, tabulated by Lander and Parkin,
Table I, row 5 (1966). The cofinal construction uses sum-and-difference
coordinates as in Browning, arXiv:1306.6767, section 3.
-/

namespace Erdos324

private def F (d x : ℤ) : ℤ := x^4 + d*x

/-- Strict input and value order records four distinct members of each. -/
private def Four (d : ℤ) (a r s b : ℕ) : Prop :=
  0 < a ∧ a < r ∧ r < s ∧ s < b ∧
  F d a < F d r ∧ F d r < F d s ∧ F d s < F d b ∧
  F d a + F d b = F d r + F d s

private def unitA : ℤ :=
  874018946343860822837210485078038130821495698266254502309463746279984552490
private def unitB : ℤ :=
  9765117676022524646156117223741039159787030310298367588081066048007235747

/-- Coordinates of the square of the positive norm-one unit. The first
coordinate is written as 1 + 2Db² to display its residue modulo D. -/
private def squareA : ℤ := 1 + 2*8011*unitB^2
private def squareB : ℤ := 2*unitA*unitB

private theorem norm_product (x y a b : ℤ) :
    (a*x+8011*b*y)^2 - 8011*(b*x+a*y)^2 =
      (a^2-8011*b^2)*(x^2-8011*y^2) := by ring

private theorem norm_conic (w y : ℤ) :
    (8011*w-4278)^2 - 8011*y^2 =
      15705720 - 8011*(y^2-(8011*w^2-8556*w+324)) := by ring

private theorem square_norm : squareA^2-8011*squareB^2=1 := by
  norm_num [squareA, squareB, unitA, unitB]

/-- Multiplying (4278,18) by the original unit gives this first positive
solution, with w=(x+4278)/8011. -/
private theorem conic_seed : ∃ w y : ℤ, 0 < w ∧ 0 < y ∧
    y^2 = 8011*w^2-8556*w+324 := by
  refine ⟨642511982412449458123081543701517599353055647717818096410685241365163062764,
    57507514452213855247325658214568851880355838236248997583381147986414676470486,
    ?_, ?_, ?_⟩ <;> norm_num

private theorem conic_step (w y : ℤ) (hw : 0 < w) (hy : 0 < y)
    (he : y^2=8011*w^2-8556*w+324) :
    ∃ w' y' : ℤ, w < w' ∧ 0 < y' ∧ y'^2=8011*w'^2-8556*w'+324 := by
  let x := 8011*w-4278
  let w' := w + 2*unitB^2*x + squareB*y
  let y' := squareB*x + squareA*y
  have hx : 0 < x := by dsimp [x]; omega
  have ha : 0 < squareA := by norm_num [squareA,unitB]
  have hb : 0 < squareB := by norm_num [squareB,unitA,unitB]
  have hg : 0 < squareB*y := mul_pos hb hy
  have hm : 0 ≤ 2*unitB^2*x := by positivity
  have grow : w < w' := by dsimp [w']; omega
  have pos : 0 < y' := by dsimp [y']; positivity
  have coordinates : 8011*w'-4278 = squareA*x+8011*squareB*y := by
    dsimp [w',squareA,x]
    ring
  have preserved : (8011*w'-4278)^2-8011*y'^2 = 15705720 := by
    rw [coordinates]
    change (squareA*x+8011*squareB*y)^2-8011*(squareB*x+squareA*y)^2 = _
    rw [norm_product, square_norm]
    dsimp [x]
    rw [norm_conic, he]
    norm_num
  rw [norm_conic] at preserved
  exact ⟨w', y', grow, pos, by linarith only [preserved]⟩

private theorem primary_conic_unbounded (N : ℕ) :
    ∃ w y : ℤ, (N : ℤ) < w ∧ 0 < y ∧ y^2 = 8011*w^2-8556*w+324 := by
  induction N with
  | zero => simpa using conic_seed
  | succ n ih =>
    obtain ⟨w,y,hw,hy,he⟩ := ih
    have hwpos : 0 < w := by omega
    obtain ⟨w',y',hg,hp,he'⟩ := conic_step w y hwpos hy he
    exact ⟨w',y',by omega,hp,he'⟩

/-- Factoring the two quartic differences recovers the conic norm equation. -/
private theorem primary_conic_factor (w y : ℤ) :
    let S := -64+1729*w
    let T := -1+1051*w
    F (-349520) (S+y) - F (-349520) (S-y) -
      (F (-349520) (T+4*y) - F (-349520) (T-4*y)) =
      -524280*w*y*(y^2-8011*w^2+8556*w-324) := by
  dsimp [F]
  ring

private theorem high_cube {a : ℤ} (h : 690 ≤ a) : 349520 < a^3 := by
  calc (349520 : ℤ) < 72^3 := by decide
       _ ≤ a^3 := by gcongr; omega

private theorem increasing_on_tail {a b : ℤ} (h : 690 ≤ a) (hab : a<b) :
    F (-349520) a < F (-349520) b := by
  have ha : 0<a := by omega
  have hb : 0<b := by omega
  have hq : 0 < b^3+b^2*a+b*a^2+a^3-349520 := by
    linarith only [high_cube h, show 0≤b^3 by positivity,
      show 0≤b^2*a by positivity, show 0≤b*a^2 by positivity]
  have hp := mul_pos (sub_pos.mpr hab) hq
  unfold F
  nlinarith only [hp]

/-- Every positive point on the indicated conic with w≥1 yields four strictly
ordered positive indices and four strictly ordered F-values. The
first index grows at least as fast as 690w. -/
private theorem primary_conic_witness (w y : ℤ) (hw : 1 ≤ w) (hy : 0 < y)
    (hcon : y^2=8011*w^2-8556*w+324) :
    let S := -64+1729*w
    let T := -1+1051*w
    let a := (T-4*y).toNat
    let r := (T+4*y).toNat
    let s := (S-y).toNat
    let b := (S+y).toNat
    690*w ≤ (a:ℤ) ∧ Four (-349520) a r s b := by
  dsimp only
  let A := -1+1051*w-4*y
  let R := -1+1051*w+4*y
  let S := -64+1729*w-y
  let B := -64+1729*w+y
  change 690*w ≤ (A.toNat:ℤ) ∧
    Four (-349520) A.toNat R.toNat S.toNat B.toNat
  have hwpos : 0<w := by omega
  have hybd : y < 90*w := by
    by_contra! he
    have hsq := (sq_le_sq₀ (show 0 ≤ 90*w by positivity) hy.le).2 he
    nlinarith only [hsq,hcon,sq_nonneg w,hw]
  have hmin : 690*w ≤ A := by dsimp [A]; omega
  have hA : 690 ≤ A := by omega
  have har : A<R := by dsimp [A,R]; omega
  have hrs : R<S := by dsimp [R,S]; omega
  have hsb : S<B := by dsimp [S,B]; omega
  have hAR : F (-349520) A < F (-349520) R := increasing_on_tail hA har
  have hRS : F (-349520) R < F (-349520) S := increasing_on_tail (by omega) hrs
  have hSB : F (-349520) S < F (-349520) B := increasing_on_tail (by omega) hsb
  have heq : F (-349520) A + F (-349520) B = F (-349520) R + F (-349520) S := by
    have hg := primary_conic_factor w y
    have hzero : y^2-8011*w^2+8556*w-324=0 := by linarith only [hcon]
    change F (-349520) B - F (-349520) S - (F (-349520) R-F (-349520) A) = _ at hg
    rw [hzero,mul_zero] at hg
    linarith only [hg]
  have cA : (A.toNat:ℤ)=A := Int.toNat_of_nonneg (by omega)
  have cR : (R.toNat:ℤ)=R := Int.toNat_of_nonneg (by omega)
  have cS : (S.toNat:ℤ)=S := Int.toNat_of_nonneg (by omega)
  have cB : (B.toNat:ℤ)=B := Int.toNat_of_nonneg (by omega)
  unfold Four
  rw [cA,cR,cS,cB]
  exact ⟨hmin,by omega,by omega,by omega,by omega,hAR,hRS,hSB,heq⟩

/-- For the prescribed coefficient, four ordered positive indices and their
four ordered values form a pair-sum collision above every cutoff. -/
private def Cofinal (d : ℤ) : Prop :=
  ∀ N : ℕ, ∃ a r s b : ℕ, N < a ∧ Four d a r s b

/-- A common positive integral dilation of the indices multiplies their
coefficient by a cube and their polynomial values by the fourth power. -/
private theorem four_cube_scale {d : ℤ} {a r s b : ℕ} (h : Four d a r s b)
    (k : ℕ) (hk : 0 < k) :
    Four (d*(k : ℤ)^3) (k*a) (k*r) (k*s) (k*b) := by
  obtain ⟨ha, har, hrs, hsb, hfar, hfrs, hfsb, heq⟩ := h
  have scale (x : ℕ) :
      F (d*(k : ℤ)^3) ((k*x : ℕ) : ℤ) = (k : ℤ)^4 * F d x := by
    unfold F
    push_cast
    ring
  unfold Four
  simp only [scale]
  have hpos : 0 < (k : ℤ)^4 := by positivity
  refine ⟨Nat.mul_pos hk ha, Nat.mul_lt_mul_of_pos_left har hk,
    Nat.mul_lt_mul_of_pos_left hrs hk, Nat.mul_lt_mul_of_pos_left hsb hk,
    mul_lt_mul_of_pos_left hfar hpos, mul_lt_mul_of_pos_left hfrs hpos,
    mul_lt_mul_of_pos_left hfsb hpos, ?_⟩
  rw [← mul_add, ← mul_add, heq]

private theorem cofinal_cube_scale {d : ℤ} (hd : Cofinal d) (k : ℕ) (hk : 0 < k) :
    Cofinal (d*(k : ℤ)^3) := by
  intro N
  obtain ⟨a,r,s,b,hN,h⟩ := hd N
  exact ⟨k*a,k*r,k*s,k*b,hN.trans_le (Nat.le_mul_of_pos_left a hk),four_cube_scale h k hk⟩

/-- A fixed coefficient with collisions in every nonnegative tail,
constructed from the integral points of the conic. -/
private theorem cofinal_neg349520 : Cofinal (-349520) := by
  intro N
  obtain ⟨w,y,hw,hy,hcon⟩ := primary_conic_unbounded N
  have h1 : 1≤w := by omega
  obtain ⟨hmin,hfour⟩ := primary_conic_witness w y h1 hy hcon
  exact ⟨_,_,_,_,by omega,hfour⟩

private theorem den_one_of_cube_dvd (b : ℕ) (hb : b^3 ∣ 4369) : b = 1 := by
  have hc := Nat.le_of_dvd (by decide : 0 < 4369) hb
  have hsmall : b < 17 := by
    by_contra! hn
    have hbig : 17^3 ≤ b^3 := Nat.pow_le_pow_left hn 3
    omega
  have hcheck : ∀ i : Fin 17, i.val^3 ∣ 4369 → i.val = 1 := by decide
  exact hcheck ⟨b,hsmall⟩ hb

/-- When 80 divides the coefficient, any rational cube root of its ratio to
−349520 has denominator one. In lowest terms, its denominator cubed divides 4369. -/
private theorem rational_cube_integral_scale (d : ℤ) (hd : d < 0) (h80 : (80 : ℤ) ∣ d)
    (hc : ∃ q : ℚ, (d : ℚ) / (-349520) = q^3) :
    ∃ k : ℕ, 0 < k ∧ d = -349520 * (k : ℤ)^3 := by
  obtain ⟨e, he⟩ := h80
  obtain ⟨q, hq⟩ := hc
  have heq : q^3 = ((-e : ℤ) : ℚ) / (4369 : ℤ) := by
    rw [← hq, he]
    push_cast
    ring
  have hdenI : ((q.den^3 : ℕ) : ℤ) ∣ 4369 := by
    rw [← Rat.den_pow, heq, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd _ _
  have hden : q.den = 1 := den_one_of_cube_dvd _ (by exact_mod_cast hdenI)
  have hint : (q.num : ℚ) = q := by
    simpa [hden] using Rat.num_div_den q
  have hidQ : (d : ℚ) = -349520*(q.num : ℚ)^3 := by
    rw [← hint] at hq
    linarith
  have hid : d = -349520*q.num^3 := by exact_mod_cast hidQ
  have hpos : 0 < q.num := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q.num) hn
    nlinarith only [hid, hd, hh]
  exact ⟨q.num.toNat, by omega, by simpa [Int.toNat_of_nonneg hpos.le] using hid⟩

/-- Both the indices and the values in a cofinal witness can exceed any
prescribed positive threshold. -/
private theorem cofinal_large_values {d : ℤ} (h : Cofinal d) (N : ℕ) :
    ∃ a r s b : ℕ, N<a ∧ (N:ℤ)<F d a ∧ Four d a r s b := by
  obtain ⟨a,r,s,b,ha,hfour⟩ := h (max N (d.natAbs+1))
  have hNa : N<a := lt_of_le_of_lt (le_max_left _ _) ha
  have hab : d.natAbs < a := by have := le_max_right N (d.natAbs+1); omega
  have hca : |d| < (a:ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hab
  have ha1 : 1 ≤ (a:ℤ) := by omega
  have hpow : (a:ℤ) ≤ (a:ℤ)^3 := by
    calc (a:ℤ) = 1*a := by ring
         _ ≤ (a:ℤ)^2*a := mul_le_mul_of_nonneg_right (one_le_pow₀ ha1) (by positivity)
         _ = _ := by ring
  have hq : 1 ≤ (a:ℤ)^3+d := by have := neg_le_abs d; omega
  have hval : (a:ℤ) ≤ F d a := by
    calc (a:ℤ) = a*1 := by ring
         _ ≤ a*((a:ℤ)^3+d) := mul_le_mul_of_nonneg_left hq (by positivity)
         _ = _ := by unfold F; ring
  exact ⟨a,r,s,b,hNa,lt_of_lt_of_le (by exact_mod_cast hNa) hval,hfour⟩

end Erdos324

open Erdos324 in
theorem solution (d : ℤ)
    (hsize : d ≤ -379828253655132800)
    (hres : (-d) % 2220222977058240 = 170124578173760)
    (hcube : ∃ q : ℚ, (d : ℚ) / (-349520) = q^3) (N : ℕ) :
    let f : ℕ → ℤ := fun x => (x : ℤ)^4 + d * (x : ℤ)
    ∃ a r s b : ℕ,
      N < a ∧ a < r ∧ r < s ∧ s < b ∧
      (N : ℤ) < f a ∧ f a < f r ∧ f r < f s ∧ f s < f b ∧
      f a + f b = f r + f s := by
  have h80 : (80 : ℤ) ∣ d := by
    refine ⟨-(2126557227172 + 27752787213228*((-d)/2220222977058240)), ?_⟩
    omega
  obtain ⟨k, hk, heq⟩ := rational_cube_integral_scale d (by omega) h80 hcube
  have hcofinal : Cofinal d := heq ▸ cofinal_cube_scale cofinal_neg349520 k hk
  obtain ⟨a,r,s,b,ha,hvalue,hfour⟩ := cofinal_large_values hcofinal N
  obtain ⟨_,har,hrs,hsb,hfar,hfrs,hfsb,hsum⟩ := hfour
  exact ⟨a,r,s,b,ha,har,hrs,hsb,hvalue,hfar,hfrs,hfsb,hsum⟩
