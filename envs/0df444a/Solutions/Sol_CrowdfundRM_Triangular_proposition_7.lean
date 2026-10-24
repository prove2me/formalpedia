-- Prove2me | solution 1 for CrowdfundRM.Triangular.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:08:33.5992+00:00
-- url     : https://prove2.me/submissions/75213eac-c5c6-4bcb-8f4f-b59af8cd51b6

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

set_option autoImplicit false
open CrowdfundRM.Triangular

namespace P7aux

/-! ### The algebraic constants -/

lemma x1_facts : 1 < x1 ∧ 2 * x1 ^ 3 - 3 * x1 ^ 2 - 3 * x1 - 2 = 0 := by
  have h37 : Real.sqrt 37 < 8 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h37' : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg _
  have hs37 := Real.sq_sqrt (show (0:ℝ) ≤ 37 by norm_num)
  set u := (8 - Real.sqrt 37) ^ ((1:ℝ) / 3) with hu
  set v := (8 + Real.sqrt 37) ^ ((1:ℝ) / 3) with hv
  have hu3 : u ^ 3 = 8 - Real.sqrt 37 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hv3 : v ^ 3 = 8 + Real.sqrt 37 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by linarith) _
  have hv0 : 0 < v := Real.rpow_pos_of_pos (by linarith) _
  have huv : u * v = 3 := by
    have h27 : (u * v) ^ 3 = (3:ℝ) ^ 3 := by
      rw [mul_pow, hu3, hv3]; nlinarith
    exact (pow_left_inj₀ (by positivity) (by norm_num) (by norm_num)).1 h27
  have hx : x1 = (1 + (u + v)) / 2 := by
    simp only [x1, hu, hv]; ring
  have hy : (u + v) ^ 3 = 16 + 9 * (u + v) := by
    linear_combination hu3 + hv3 + 3 * (u + v) * huv
  rw [hx]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (u + v), sq_nonneg (u + v - 1)]
  · linear_combination (1 / 4 : ℝ) * hy

lemma x0_facts : ∃ t : ℝ, 1 < t ∧ x0 = t ^ 2 ∧ t ^ 4 + t ^ 3 - 3 * t ^ 2 - t - 1 = 0 := by
  set c := (11:ℝ) ^ ((1:ℝ) / 3) with hc
  have hc3 : c ^ 3 = 11 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hc2 : 2 < c := by nlinarith [sq_nonneg (c - 2), sq_nonneg c]
  have hc94 : c < 9 / 4 := by nlinarith [sq_nonneg (c - 9/4), sq_nonneg c]
  set d := Real.sqrt (9 - 4 * c) with hd
  have hd2 : d ^ 2 = 9 - 4 * c := Real.sq_sqrt (by linarith)
  have hd0 : 0 < d := Real.sqrt_pos.2 (by linarith)
  have hd1 : d < 1 := by nlinarith
  have hfd : 5 / (2 * d) = d * (8 * c ^ 2 / 5 + 18 * c / 5 + 81 / 10) := by
    field_simp
    nlinarith [hd2, hc3]
  set e := Real.sqrt (9 / 2 + c + 5 / (2 * d)) with he
  have hpos : 0 < 9 / 2 + c + 5 / (2 * d) := by positivity
  have he2' : e ^ 2 = 9 / 2 + c + 5 / (2 * d) := Real.sq_sqrt hpos.le
  have h52 : 5 / 2 < 5 / (2 * d) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have he3 : 3 < e := by nlinarith [Real.sqrt_nonneg (9 / 2 + c + 5 / (2 * d))]
  have he2 : e ^ 2 = 9 / 2 + c + d * (8 * c ^ 2 / 5 + 18 * c / 5 + 81 / 10) := by
    rw [he2', hfd]
  refine ⟨(-1 - d + 2 * e) / 4, by linarith, ?_, ?_⟩
  · simp only [x0, hc, hd, he]; ring
  · linear_combination
      (c^2*d/10 + 9*c*d/40 + c/16 + 3*d^2/32 - d*e/8 + 81*d/160 + e^2/16 - 9/16) * he2 +
      (4*c^4/25 + 18*c^3/25 + 3*c^2*d/20 - c^2*e/5 + 243*c^2/100 + 27*c*d/80 - 9*c*e/20
        + 5957*c/1600 + d^2/256 - d*e/32 + 243*d/320 - 81*e/80 + 27819/6400) * hd2 +
      (-16*c^2/25 - 36*c/25 - 2*d/5 + 4*e/5 - 81/25) * hc3

/-! ### Part (a), mode 0: algebraic optimization -/

/-- `F0 a X = ((1-a)^3 - (1-aX)^3)/X` -/
noncomputable def F0 (a X : ℝ) : ℝ := ((1 - a) ^ 3 - (1 - a * X) ^ 3) / X

lemma rho_le (t : ℝ) (ht : 1 < t) (hP : t ^ 4 + t ^ 3 - 3 * t ^ 2 - t - 1 = 0)
    (s : ℝ) (hs : 1 ≤ s) :
    (s - 1) * (s + 1) ^ 3 * (t ^ 2 * (t ^ 2 + t + 1) ^ 2) ≤
      (t - 1) * (t + 1) ^ 3 * (s ^ 2 * (s ^ 2 + s + 1) ^ 2) ∧
    ((s - 1) * (s + 1) ^ 3 * (t ^ 2 * (t ^ 2 + t + 1) ^ 2) =
      (t - 1) * (t + 1) ^ 3 * (s ^ 2 * (s ^ 2 + s + 1) ^ 2) → s = t) := by
  have hQ : 0 < (t^3+3*t^2-t)*s^4+(6*t^3+10*t^2+2)*s^3+(10*t^3+20*t^2+4*t+5)*s^2
      +(6*t^3+18*t^2+6*t+6)*s+(t^3+6*t^2+3*t+2) := by
    have h1 : 0 < t^3+3*t^2-t := by nlinarith
    positivity
  have hid : (t - 1) * (t + 1) ^ 3 * (s ^ 2 * (s ^ 2 + s + 1) ^ 2) -
      (s - 1) * (s + 1) ^ 3 * (t ^ 2 * (t ^ 2 + t + 1) ^ 2) =
      (s - t) ^ 2 * ((t^3+3*t^2-t)*s^4+(6*t^3+10*t^2+2)*s^3+(10*t^3+20*t^2+4*t+5)*s^2
      +(6*t^3+18*t^2+6*t+6)*s+(t^3+6*t^2+3*t+2)) := by
    linear_combination (s^6 + 4*s^5 - s^4*t^2 - 2*s^4*t + 8*s^4 - 2*s^3*t^2 - 8*s^3*t + 8*s^3
      - 10*s^2*t + 3*s^2 + 2*s*t^2 - 4*s*t + t^2) * hP
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (s - t)) hQ.le]
  · intro h
    have : (s - t) ^ 2 * ((t^3+3*t^2-t)*s^4+(6*t^3+10*t^2+2)*s^3+(10*t^3+20*t^2+4*t+5)*s^2
      +(6*t^3+18*t^2+6*t+6)*s+(t^3+6*t^2+3*t+2)) = 0 := by rw [← hid]; linarith
    rcases mul_eq_zero.1 this with h | h
    · nlinarith [sq_nonneg (s - t), pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h]
    · linarith

lemma k_le (s a : ℝ) (hs : 1 < s) (ha : 0 < a) (has : a * s ^ 2 ≤ 1) :
    3 * a - 3 * a ^ 2 * (s ^ 2 + 1) + a ^ 3 * (s ^ 4 + s ^ 2 + 1) ≤
      (s + 1) ^ 2 / (s ^ 2 + s + 1) ^ 2 ∧
    (3 * a - 3 * a ^ 2 * (s ^ 2 + 1) + a ^ 3 * (s ^ 4 + s ^ 2 + 1) =
      (s + 1) ^ 2 / (s ^ 2 + s + 1) ^ 2 → a = 1 / (s ^ 2 + s + 1)) := by
  have hq : 0 < s ^ 2 + s + 1 := by positivity
  have hid : (s + 1) ^ 2 / (s ^ 2 + s + 1) ^ 2 -
      (3 * a - 3 * a ^ 2 * (s ^ 2 + 1) + a ^ 3 * (s ^ 4 + s ^ 2 + 1)) =
      (a * (s ^ 2 + s + 1) - 1) ^ 2 * ((s + 1) ^ 2 - a * (s ^ 4 + s ^ 2 + 1)) /
        (s ^ 2 + s + 1) ^ 2 := by
    field_simp; ring
  have hg : 0 < (s + 1) ^ 2 - a * (s ^ 4 + s ^ 2 + 1) := by
    have h2 : s ^ 2 * ((s + 1) ^ 2 - a * (s ^ 4 + s ^ 2 + 1)) ≥ 2 * s ^ 3 - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right has (show 0 ≤ s ^ 4 + s ^ 2 + 1 by positivity)]
    have h3 : 0 < 2 * s ^ 3 - 1 := by nlinarith
    by_contra hc
    have hc := not_lt.1 hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hc]
  constructor
  · have : 0 ≤ (a * (s ^ 2 + s + 1) - 1) ^ 2 * ((s + 1) ^ 2 - a * (s ^ 4 + s ^ 2 + 1)) /
        (s ^ 2 + s + 1) ^ 2 := by positivity
    linarith
  · intro h
    have h0 : (a * (s ^ 2 + s + 1) - 1) ^ 2 * ((s + 1) ^ 2 - a * (s ^ 4 + s ^ 2 + 1)) /
        (s ^ 2 + s + 1) ^ 2 = 0 := by rw [← hid]; linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h1
        field_simp; linarith
      · linarith
    · exact absurd h0 (by positivity)

lemma F0_core (t : ℝ) (ht : 1 < t) (hP : t ^ 4 + t ^ 3 - 3 * t ^ 2 - t - 1 = 0)
    (a X : ℝ) (ha : 0 < a) (hX : 1 ≤ X) (haX : a * X ≤ 1) :
    F0 a X ≤ F0 (1 / (t ^ 2 + t + 1)) (t ^ 2) ∧
    (F0 a X = F0 (1 / (t ^ 2 + t + 1)) (t ^ 2) → a = 1 / (t ^ 2 + t + 1) ∧ X = t ^ 2) := by
  -- value at the optimum
  have hval : ∀ s : ℝ, 1 < s → ∀ b : ℝ, F0 b (s ^ 2) =
      (s ^ 2 - 1) * (3 * b - 3 * b ^ 2 * (s ^ 2 + 1) + b ^ 3 * (s ^ 4 + s ^ 2 + 1)) / s ^ 2 := by
    intro s hs b; unfold F0; congr 1; ring
  have hNt : 0 < (t - 1) * (t + 1) ^ 3 / (t ^ 2 * (t ^ 2 + t + 1) ^ 2) := by
    have : 0 < t - 1 := by linarith
    positivity
  have hstar : F0 (1 / (t ^ 2 + t + 1)) (t ^ 2) =
      (t - 1) * (t + 1) ^ 3 / (t ^ 2 * (t ^ 2 + t + 1) ^ 2) := by
    rw [hval t ht]
    have hq : 0 < t ^ 2 + t + 1 := by positivity
    field_simp; ring
  rw [hstar]
  set s := Real.sqrt X with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.2 hX
  have hXs : X = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  rw [hXs] at haX ⊢
  rcases eq_or_lt_of_le hs1 with h1 | h1
  · -- s = 1
    rw [← h1]
    have : F0 a ((1:ℝ) ^ 2) = 0 := by unfold F0; ring
    rw [this]
    exact ⟨hNt.le, fun h => by linarith⟩
  · obtain ⟨hk, hkeq⟩ := k_le s a h1 ha haX
    obtain ⟨hr, hreq⟩ := rho_le t ht hP s hs1
    have hs0 : 0 < s := by linarith
    have hq : 0 < s ^ 2 + s + 1 := by positivity
    have hA : 0 < (s ^ 2 - 1) / s ^ 2 := by
      have : 0 < s ^ 2 - 1 := by nlinarith
      positivity
    have hF : F0 a (s ^ 2) = (s ^ 2 - 1) / s ^ 2 *
        (3 * a - 3 * a ^ 2 * (s ^ 2 + 1) + a ^ 3 * (s ^ 4 + s ^ 2 + 1)) := by
      rw [hval s h1]; ring
    have hNs : (s ^ 2 - 1) / s ^ 2 * ((s + 1) ^ 2 / (s ^ 2 + s + 1) ^ 2) =
        (s - 1) * (s + 1) ^ 3 / (s ^ 2 * (s ^ 2 + s + 1) ^ 2) := by
      field_simp; ring
    have hmid : F0 a (s ^ 2) ≤ (s - 1) * (s + 1) ^ 3 / (s ^ 2 * (s ^ 2 + s + 1) ^ 2) := by
      rw [hF, ← hNs]; exact mul_le_mul_of_nonneg_left hk hA.le
    have hrho : (s - 1) * (s + 1) ^ 3 / (s ^ 2 * (s ^ 2 + s + 1) ^ 2) ≤
        (t - 1) * (t + 1) ^ 3 / (t ^ 2 * (t ^ 2 + t + 1) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; exact hr
    refine ⟨hmid.trans hrho, fun heq => ?_⟩
    have he1 : (s - 1) * (s + 1) ^ 3 / (s ^ 2 * (s ^ 2 + s + 1) ^ 2) =
        (t - 1) * (t + 1) ^ 3 / (t ^ 2 * (t ^ 2 + t + 1) ^ 2) := le_antisymm hrho (heq ▸ hmid)
    rw [div_eq_div_iff (by positivity) (by positivity)] at he1
    have hst : s = t := hreq he1
    subst hst
    refine ⟨?_, rfl⟩
    apply hkeq
    have h2 : F0 a (s ^ 2) = (s ^ 2 - 1) / s ^ 2 * ((s + 1) ^ 2 / (s ^ 2 + s + 1) ^ 2) := by
      rw [hNs]; exact heq
    rw [hF] at h2
    exact mul_left_cancel₀ hA.ne' h2

/-! ### Part (a), mode v̄ -/

/-- `H1 a X = a((X-1) - a^2(X^3-1)/3)/X` -/
noncomputable def H1 (a X : ℝ) : ℝ := a * ((X - 1) - a ^ 2 * (X ^ 3 - 1) / 3) / X

lemma psi_le (t : ℝ) (ht : 1 < t) (hP : 2 * t ^ 3 - 3 * t ^ 2 - 3 * t - 2 = 0)
    (s : ℝ) (hs : 1 ≤ s) :
    (s - 1) ^ 2 * (t ^ 2 * (t ^ 2 + t + 1)) ≤ (t - 1) ^ 2 * (s ^ 2 * (s ^ 2 + s + 1)) ∧
    ((s - 1) ^ 2 * (t ^ 2 * (t ^ 2 + t + 1)) = (t - 1) ^ 2 * (s ^ 2 * (s ^ 2 + s + 1)) →
      s = t) := by
  have hQ : 0 < (t - 1) ^ 2 * s ^ 2 + 3 * (t + 1) * s - (t ^ 2 + t + 1) := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (show 0 ≤ s ^ 2 - 1 by nlinarith)]
  have hid : (t - 1) ^ 2 * (s ^ 2 * (s ^ 2 + s + 1)) - (s - 1) ^ 2 * (t ^ 2 * (t ^ 2 + t + 1)) =
      (s - t) ^ 2 * ((t - 1) ^ 2 * s ^ 2 + 3 * (t + 1) * s - (t ^ 2 + t + 1)) := by
    linear_combination (s^3 - s^2*t - s^2 + s*t) * hP
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (s - t)) hQ.le]
  · intro h
    have : (s - t) ^ 2 * ((t - 1) ^ 2 * s ^ 2 + 3 * (t + 1) * s - (t ^ 2 + t + 1)) = 0 := by
      rw [← hid]; linarith
    rcases mul_eq_zero.1 this with h | h
    · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h]
    · linarith

lemma H1_core (t : ℝ) (ht : 1 < t) (hP : 2 * t ^ 3 - 3 * t ^ 2 - 3 * t - 2 = 0)
    (a X : ℝ) (ha : 0 < a) (hX : 1 ≤ X) (haX : a * X ≤ 1) :
    H1 a X ≤ H1 (1 / Real.sqrt (1 + t + t ^ 2)) t ∧
    (H1 a X = H1 (1 / Real.sqrt (1 + t + t ^ 2)) t →
      a = 1 / Real.sqrt (1 + t + t ^ 2) ∧ X = t) := by
  -- general bound for fixed X
  have gen : ∀ Y : ℝ, 1 ≤ Y → ∀ b : ℝ, 0 < b →
      H1 b Y ≤ 2 / 3 * ((Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2))) ∧
      (1 < Y → H1 b Y = 2 / 3 * ((Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2))) →
        b = 1 / Real.sqrt (1 + Y + Y ^ 2)) := by
    intro Y hY b hb
    set m := Real.sqrt (1 + Y + Y ^ 2) with hm
    have hm0 : 0 < m := Real.sqrt_pos.2 (by positivity)
    have hm2 : m ^ 2 = 1 + Y + Y ^ 2 := Real.sq_sqrt (by positivity)
    have hY0 : 0 < Y := by linarith
    have hid : 2 / 3 * ((Y - 1) / (Y * m)) - H1 b Y =
        (Y - 1) / Y * ((b * m - 1) ^ 2 * (b * m + 2) / (3 * m)) := by
      unfold H1
      have : Y ^ 3 - 1 = (Y - 1) * m ^ 2 := by rw [hm2]; ring
      rw [this]
      field_simp; ring
    have hnn : 0 ≤ (Y - 1) / Y * ((b * m - 1) ^ 2 * (b * m + 2) / (3 * m)) := by
      have : 0 ≤ Y - 1 := by linarith
      positivity
    refine ⟨by linarith, fun hY1 heq => ?_⟩
    have h0 : (Y - 1) / Y * ((b * m - 1) ^ 2 * (b * m + 2) / (3 * m)) = 0 := by
      rw [← hid]; linarith
    have hA : (Y - 1) / Y ≠ 0 := by
      have : 0 < Y - 1 := by linarith
      positivity
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hA
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h
          field_simp; linarith
        · nlinarith
      · exact absurd h (by positivity)
  -- the comparison of φ(Y) = (Y-1)/(Y m(Y))
  have phi_le : ∀ Y : ℝ, 1 ≤ Y →
      (Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2)) ≤ (t - 1) / (t * Real.sqrt (1 + t + t ^ 2)) ∧
      ((Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2)) = (t - 1) / (t * Real.sqrt (1 + t + t ^ 2)) →
        Y = t) := by
    intro Y hY
    obtain ⟨h1, h2⟩ := psi_le t ht hP Y hY
    have hmY0 : 0 < Real.sqrt (1 + Y + Y ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hmt0 : 0 < Real.sqrt (1 + t + t ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hmY2 : Real.sqrt (1 + Y + Y ^ 2) ^ 2 = 1 + Y + Y ^ 2 := Real.sq_sqrt (by positivity)
    have hmt2 : Real.sqrt (1 + t + t ^ 2) ^ 2 = 1 + t + t ^ 2 := Real.sq_sqrt (by positivity)
    have hu : 0 ≤ (Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2)) := by
      have : 0 ≤ Y - 1 := by linarith
      have : 0 < Y := by linarith
      positivity
    have hv : 0 ≤ (t - 1) / (t * Real.sqrt (1 + t + t ^ 2)) := by
      have : 0 ≤ t - 1 := by linarith
      have : 0 < t := by linarith
      positivity
    have hsq : ∀ Z : ℝ, 0 < Z → ((Z - 1) / (Z * Real.sqrt (1 + Z + Z ^ 2))) ^ 2 =
        (Z - 1) ^ 2 / (Z ^ 2 * (Z ^ 2 + Z + 1)) := by
      intro Z hZ
      have hm2 : Real.sqrt (1 + Z + Z ^ 2) ^ 2 = 1 + Z + Z ^ 2 := Real.sq_sqrt (by positivity)
      rw [div_pow, mul_pow, hm2]; ring
    have hY0 : 0 < Y := by linarith
    have ht0 : 0 < t := by linarith
    have hsqle : ((Y - 1) / (Y * Real.sqrt (1 + Y + Y ^ 2))) ^ 2 ≤
        ((t - 1) / (t * Real.sqrt (1 + t + t ^ 2))) ^ 2 := by
      rw [hsq Y hY0, hsq t ht0, div_le_div_iff₀ (by positivity) (by positivity)]
      exact h1
    refine ⟨(pow_le_pow_iff_left₀ hu hv two_ne_zero).1 hsqle, fun heq => h2 ?_⟩
    have := congrArg (· ^ 2) heq
    rw [hsq Y hY0, hsq t ht0, div_eq_div_iff (by positivity) (by positivity)] at this
    exact this
  have hstar : H1 (1 / Real.sqrt (1 + t + t ^ 2)) t =
      2 / 3 * ((t - 1) / (t * Real.sqrt (1 + t + t ^ 2))) := by
    have hmt0 : 0 < Real.sqrt (1 + t + t ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hmt2 : Real.sqrt (1 + t + t ^ 2) ^ 2 = 1 + t + t ^ 2 := Real.sq_sqrt (by positivity)
    have ht0 : 0 < t := by linarith
    unfold H1
    have : t ^ 3 - 1 = (t - 1) * Real.sqrt (1 + t + t ^ 2) ^ 2 := by rw [hmt2]; ring
    rw [this]
    field_simp; ring
  rw [hstar]
  obtain ⟨g1, g2⟩ := gen X hX a ha
  obtain ⟨p1, p2⟩ := phi_le X hX
  refine ⟨g1.trans (by linarith), fun heq => ?_⟩
  have hXt : X = t := by
    apply p2
    have : 2 / 3 * ((X - 1) / (X * Real.sqrt (1 + X + X ^ 2))) =
        2 / 3 * ((t - 1) / (t * Real.sqrt (1 + t + t ^ 2))) := le_antisymm (by linarith)
          (heq ▸ g1)
    linarith
  subst hXt
  exact ⟨g2 ht (by rw [heq]), rfl⟩

/-! ### Calculus helpers -/

lemma signs (φ φ' : ℝ → ℝ) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (hder : ∀ x, 0 < x → HasDerivAt φ (φ' x) x)
    (hneg : ∀ x, 0 < x → x < d → φ' x < 0) (hpos : ∀ x, d < x → x < 1 → 0 < φ' x)
    (h1 : φ 1 = 0) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hc : φ c = 0) :
    c < d ∧ (∀ x, 0 < x → x < c → 0 < φ x) ∧ (∀ x, c < x → x < 1 → φ x < 0) := by
  have anti : StrictAntiOn φ (Set.Ioc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 d)
    · exact fun x hx => (hder x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hder x hx.1).deriv]; exact hneg x hx.1 hx.2
  have mono : StrictMonoOn φ (Set.Icc d 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc d 1)
    · exact fun x hx => (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hder x (by linarith [hx.1])).deriv]; exact hpos x hx.1 hx.2
  have neg1 : ∀ x, d ≤ x → x < 1 → φ x < 0 := by
    intro x hx hx1
    have := mono ⟨hx, hx1.le⟩ ⟨hd1.le, le_rfl⟩ hx1
    linarith
  have hcd : c < d := by
    by_contra h
    have := neg1 c (not_lt.1 h) hc1
    linarith
  refine ⟨hcd, fun x hx0 hxc => ?_, fun x hcx hx1 => ?_⟩
  · have := anti ⟨hx0, by linarith⟩ ⟨hc0, hcd.le⟩ hxc
    linarith
  · rcases le_or_gt x d with hxd | hxd
    · have := anti ⟨hc0, hcd.le⟩ ⟨by linarith, hxd⟩ hcx
      linarith
    · exact neg1 x hxd.le hx1

lemma umax (h φ : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hder : ∀ x, 0 < x → HasDerivAt h (φ x) x)
    (hpos : ∀ x, 0 < x → x < c → 0 < φ x) (hneg : ∀ x, c < x → x < 1 → φ x < 0) :
    ∀ x, 0 < x → x ≤ 1 → x ≠ c → h x < h c := by
  have mono : StrictMonoOn h (Set.Ioc 0 c) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 c)
    · exact fun x hx => (hder x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hder x hx.1).deriv]; exact hpos x hx.1 hx.2
  have anti : StrictAntiOn h (Set.Icc c 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c 1)
    · exact fun x hx => (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hder x (by linarith [hx.1])).deriv]; exact hneg x hx.1 hx.2
  intro x hx0 hx1 hxc
  rcases lt_or_gt_of_ne hxc with h' | h'
  · exact mono ⟨hx0, h'.le⟩ ⟨hc0, le_rfl⟩ h'
  · exact anti ⟨le_rfl, hc1.le⟩ ⟨h'.le, hx1⟩ h'

lemma m0pos (τ : ℝ) (h0 : 0 < τ) (h1 : τ < 1) :
    0 < -Real.log τ - 3 / 2 + 2 * τ - τ ^ 2 / 2 := by
  have anti : StrictAntiOn (fun τ : ℝ => -Real.log τ - 3 / 2 + 2 * τ - τ ^ 2 / 2)
      (Set.Ioc 0 1) := by
    have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun τ : ℝ => -Real.log τ - 3 / 2 + 2 * τ - τ ^ 2 / 2)
        (-x⁻¹ + 2 - x) x := by
      intro x hx
      have := ((((Real.hasDerivAt_log hx.ne').neg).sub_const (3 / 2)).add
        ((hasDerivAt_id x).const_mul 2)).sub ((hasDerivAt_pow 2 x).div_const 2)
      exact this.congr_deriv (by norm_num <;> ring)
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
    · exact fun x hx => (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd x hx.1).deriv]
      have hx0 := hx.1.ne'
      have : -x⁻¹ + 2 - x = -((1 - x) ^ 2 / x) := by field_simp; ring
      rw [this]
      have : 0 < (1 - x) ^ 2 / x := by
        have : 0 < 1 - x := by linarith [hx.2]
        have := hx.1
        positivity
      linarith
  have := anti ⟨h0, h1.le⟩ ⟨one_pos, le_rfl⟩ h1
  simp at this
  linarith

lemma m1pos (τ : ℝ) (h0 : 0 < τ) (h1 : τ < 1) :
    0 < -Real.log τ - (1 - τ ^ 2) / 2 := by
  have := Real.log_lt_sub_one_of_pos h0 h1.ne
  nlinarith [sq_nonneg (1 - τ)]

/-- `h0` and its derivative for part (b), mode 0. -/
noncomputable def hb0 (β : ℝ) : ℝ := β * (-Real.log β - 2 * (1 - β) + (1 - β ^ 2) / 2)
noncomputable def φb0 (β : ℝ) : ℝ := -Real.log β - 5 / 2 + 4 * β - 3 * β ^ 2 / 2

lemma hb0_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt hb0 (φb0 x) x := by
  have hi : HasDerivAt (fun β : ℝ => -Real.log β - 2 * (1 - β) + (1 - β ^ 2) / 2)
      (-x⁻¹ + 2 - x) x := by
    have := (((Real.hasDerivAt_log hx.ne').neg).sub
      (((hasDerivAt_id' x).const_sub 1).const_mul 2)).add
      (((hasDerivAt_pow 2 x).const_sub 1).div_const 2)
    exact this.congr_deriv (by norm_num <;> ring)
  have := (hasDerivAt_id' x).mul hi
  unfold hb0 φb0
  exact this.congr_deriv (by field_simp; ring)

lemma φb0_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt φb0 (-x⁻¹ + 4 - 3 * x) x := by
  have := ((((Real.hasDerivAt_log hx.ne').neg).sub_const (5 / 2)).add
    ((hasDerivAt_id' x).const_mul 4)).sub ((hasDerivAt_pow 2 x).const_mul 3 |>.div_const 2)
  unfold φb0
  exact this.congr_deriv (by norm_num <;> ring)

lemma b0_signs (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hc : φb0 c = 0) :
    c < 1 / 3 ∧ (∀ x, 0 < x → x < c → 0 < φb0 x) ∧ (∀ x, c < x → x < 1 → φb0 x < 0) := by
  apply signs φb0 (fun x => -x⁻¹ + 4 - 3 * x) (1 / 3) (by norm_num) (by norm_num)
    φb0_deriv _ _ (by simp [φb0]; norm_num) c hc0 hc1 hc
  · intro x hx0 hx
    have : -x⁻¹ + 4 - 3 * x = -((3 * x - 1) * (x - 1) / x) := by field_simp; ring
    simp only [this]
    have : 0 < (3 * x - 1) * (x - 1) / x :=
      div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) hx0
    linarith
  · intro x hx0 hx
    have hx0' : 0 < x := by linarith
    have : -x⁻¹ + 4 - 3 * x = -((3 * x - 1) * (x - 1) / x) := by field_simp; ring
    simp only [this]
    have : (3 * x - 1) * (x - 1) / x < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hx0'
    linarith

lemma b0_exists : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ φb0 c = 0 := by
  have hε0 : 0 < Real.exp (-3) := Real.exp_pos _
  have hε : Real.exp (-3) < 1 / 3 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_lt_exp (show (3:ℝ) ≠ 0 by norm_num)
    norm_num at this ⊢; linarith
  have hcont : ContinuousOn φb0 (Set.Icc (Real.exp (-3)) (1 / 3)) := by
    intro x hx
    exact (φb0_deriv x (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hlo : φb0 (1 / 3) < 0 := by
    unfold φb0
    have : Real.log 3 < 4 / 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have h2 := Real.add_one_le_exp (1 / 3 : ℝ)
      have : Real.exp (4 / 3) = Real.exp 1 * Real.exp (1 / 3) := by
        rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    rw [one_div, Real.log_inv]; linarith
  have hhi : 0 < φb0 (Real.exp (-3)) := by
    unfold φb0; rw [Real.log_exp]; nlinarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hε.le hcont ⟨hlo.le, hhi.le⟩
  refine ⟨c, by linarith [hc.1], by linarith [hc.2], hcv⟩

/-- part (b), mode v̄. -/
noncomputable def hb1 (a : ℝ) : ℝ := a * (-Real.log a - (1 - a ^ 2) / 2)
noncomputable def φb1 (a : ℝ) : ℝ := -Real.log a - 3 / 2 + 3 * a ^ 2 / 2

lemma hb1_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt hb1 (φb1 x) x := by
  have hi : HasDerivAt (fun β : ℝ => -Real.log β - (1 - β ^ 2) / 2) (-x⁻¹ + x) x := by
    have := ((Real.hasDerivAt_log hx.ne').neg).sub
      (((hasDerivAt_pow 2 x).const_sub 1).div_const 2)
    exact this.congr_deriv (by norm_num <;> ring)
  have := (hasDerivAt_id' x).mul hi
  unfold hb1 φb1
  exact this.congr_deriv (by field_simp; ring)

lemma φb1_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt φb1 (-x⁻¹ + 3 * x) x := by
  have := (((Real.hasDerivAt_log hx.ne').neg).sub_const (3 / 2)).add
    ((hasDerivAt_pow 2 x).const_mul 3 |>.div_const 2)
  unfold φb1
  exact this.congr_deriv (by norm_num <;> ring)

lemma b1_signs (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hc : φb1 c = 0) :
    (∀ x, 0 < x → x < c → 0 < φb1 x) ∧ (∀ x, c < x → x < 1 → φb1 x < 0) := by
  have hd2 : Real.sqrt (1 / 3) ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hd0 : 0 < Real.sqrt (1 / 3) := Real.sqrt_pos.2 (by norm_num)
  have hd1 : Real.sqrt (1 / 3) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  refine (signs φb1 (fun x => -x⁻¹ + 3 * x) (Real.sqrt (1 / 3)) hd0 hd1
    φb1_deriv ?_ ?_ (by simp [φb1]) c hc0 hc1 hc).2
  · intro x hx0 hx
    have : -x⁻¹ + 3 * x = (3 * x ^ 2 - 1) / x := by field_simp; ring
    simp only [this]
    have : x ^ 2 < 1 / 3 := by nlinarith
    exact div_neg_of_neg_of_pos (by linarith) hx0
  · intro x hx0 hx
    have hx0' : 0 < x := by linarith
    have : -x⁻¹ + 3 * x = (3 * x ^ 2 - 1) / x := by field_simp; ring
    simp only [this]
    have : 1 / 3 < x ^ 2 := by nlinarith
    exact div_pos (by linarith) hx0'

lemma w_exists_unique : ∃! w : ℝ, -1 < w ∧ w < 0 ∧ w * Real.exp w = -3 * Real.exp (-3) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun w : ℝ => w * Real.exp w) (1 * Real.exp x + x * Real.exp x) x :=
    fun x => (hasDerivAt_id' x).mul (Real.hasDerivAt_exp x)
  have mono : StrictMonoOn (fun w : ℝ => w * Real.exp w) (Set.Icc (-1) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (-1) 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      have := Real.exp_pos x
      nlinarith [hx.1]
  have he2 : 3 * Real.exp (-3) < Real.exp (-1) := by
    have : Real.exp (-1) = Real.exp 2 * Real.exp (-3) := by rw [← Real.exp_add]; norm_num
    rw [this]
    have := Real.add_one_lt_exp (show (2:ℝ) ≠ 0 by norm_num)
    have := Real.exp_pos (-3)
    nlinarith
  have hcont : ContinuousOn (fun w : ℝ => w * Real.exp w) (Set.Icc (-1) 0) :=
    fun x _ => (hd x).continuousAt.continuousWithinAt
  have h3 : 0 < Real.exp (-3) := Real.exp_pos _
  obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc (show (-1:ℝ) ≤ 0 by norm_num) hcont
    (show -3 * Real.exp (-3) ∈ Set.Icc ((-1) * Real.exp (-1)) (0 * Real.exp 0) from
      ⟨by linarith, by simp; linarith⟩)
  simp only at hwv
  have hw1 : -1 < w := by
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h] at hwv; linarith
    · exact h
  have hw0 : w < 0 := by
    rcases eq_or_lt_of_le hw.2 with h | h
    · rw [h] at hwv; simp at hwv
    · exact h
  refine ⟨w, ⟨hw1, hw0, hwv⟩, fun y ⟨hy1, hy0, hyv⟩ => ?_⟩
  exact mono.injOn ⟨hy1.le, hy0.le⟩ ⟨hw1.le, hw0.le⟩ (by rw [hyv, hwv])

lemma w_root (w : ℝ) (hw1 : -1 < w) (hw0 : w < 0) (hw : w * Real.exp w = -3 * Real.exp (-3)) :
    0 < Real.sqrt (-w / 3) ∧ Real.sqrt (-w / 3) < 1 ∧ φb1 (Real.sqrt (-w / 3)) = 0 := by
  have hpos : 0 < -w / 3 := by linarith
  refine ⟨Real.sqrt_pos.2 hpos, by rw [Real.sqrt_lt' one_pos]; linarith, ?_⟩
  have hl : Real.log (-w / 3) + w = -3 := by
    have : (-w / 3) * Real.exp w = Real.exp (-3) := by linarith
    have := congrArg Real.log this
    rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
    exact this
  unfold φb1
  rw [Real.log_sqrt hpos.le, Real.sq_sqrt hpos.le]
  linarith

/-! ### Integrals -/

lemma hE (r x : ℝ) : HasDerivAt (fun x => Real.exp (r * x)) (Real.exp (r * x) * r) x := by
  have := ((hasDerivAt_id' x).const_mul r).exp
  exact this.congr_deriv (by ring)

lemma int0 (r a T : ℝ) (hr : 0 < r) (ha : a ≠ 0) :
    ∫ x in (0:ℝ)..T, Real.exp (r * x) * (1 - a * Real.exp (r * x)) ^ 2 =
      ((1 - a) ^ 3 - (1 - a * Real.exp (r * T)) ^ 3) / (3 * a * r) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) T, HasDerivAt
      (fun x => -(1 - a * Real.exp (r * x)) ^ 3 / (3 * a * r))
      (Real.exp (r * x) * (1 - a * Real.exp (r * x)) ^ 2) x := by
    intro x _
    have := ((((hE r x).const_mul a).const_sub 1).pow 3).neg.div_const (3 * a * r)
    refine this.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp; ring
  · apply Continuous.intervalIntegrable; fun_prop

lemma int1 (r a T : ℝ) (hr : 0 < r) :
    ∫ x in (0:ℝ)..T, Real.exp (r * x) * (1 - (a * Real.exp (r * x)) ^ 2) =
      (Real.exp (r * T) - 1) / r - a ^ 2 * (Real.exp (r * T) ^ 3 - 1) / (3 * r) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) T, HasDerivAt
      (fun x => Real.exp (r * x) / r - a ^ 2 * Real.exp (r * x) ^ 3 / (3 * r))
      (Real.exp (r * x) * (1 - (a * Real.exp (r * x)) ^ 2)) x := by
    intro x _
    have := ((hE r x).div_const r).sub ((((hE r x).pow 3).const_mul (a ^ 2)).div_const (3 * r))
    refine this.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp; field_simp; ring
  · apply Continuous.intervalIntegrable; fun_prop

lemma int2 (r a T : ℝ) (hr : 0 < r) :
    ∫ y in (0:ℝ)..T, (1 - a * Real.exp (r * y)) ^ 2 =
      T - 2 * a * (Real.exp (r * T) - 1) / r + a ^ 2 * (Real.exp (r * T) ^ 2 - 1) / (2 * r) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) T, HasDerivAt
      (fun x => x - 2 * a * Real.exp (r * x) / r + a ^ 2 * Real.exp (r * x) ^ 2 / (2 * r))
      ((1 - a * Real.exp (r * x)) ^ 2) x := by
    intro x _
    have := ((hasDerivAt_id' x).sub (((hE r x).const_mul (2 * a)).div_const r)).add
      ((((hE r x).pow 2).const_mul (a ^ 2)).div_const (2 * r))
    refine this.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp; field_simp; ring
  · apply Continuous.intervalIntegrable; fun_prop

lemma int3 (r a T : ℝ) (hr : 0 < r) :
    ∫ y in (0:ℝ)..T, (1 - (a * Real.exp (r * y)) ^ 2) =
      T - a ^ 2 * (Real.exp (r * T) ^ 2 - 1) / (2 * r) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) T, HasDerivAt
      (fun x => x - a ^ 2 * Real.exp (r * x) ^ 2 / (2 * r))
      (1 - (a * Real.exp (r * x)) ^ 2) x := by
    intro x _
    have := (hasDerivAt_id' x).sub ((((hE r x).pow 2).const_mul (a ^ 2)).div_const (2 * r))
    refine this.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp; field_simp; ring
  · apply Continuous.intervalIntegrable; fun_prop

/-! ### The model -/

lemma feas (M : Campaign) (hM : M.Standing) (p T : ℝ) (h : M.Feasible p T) :
    0 < p / M.vbar ∧ p / M.vbar ≤ 1 ∧ 1 ≤ Real.exp (M.r * T) ∧
      p / M.vbar * Real.exp (M.r * T) ≤ 1 ∧
      (∀ x ∈ Set.uIcc (0:ℝ) T, 0 ≤ p * Real.exp (M.r * x) ∧ p * Real.exp (M.r * x) ≤ M.vbar) := by
  obtain ⟨_, _, hr, hv, _⟩ := hM
  obtain ⟨hp, hpv, hT0, hT⟩ := h
  have hrT : M.r * T ≤ Real.log (M.vbar / p) := by
    rw [le_div_iff₀ hr] at hT; linarith
  have hX : Real.exp (M.r * T) ≤ M.vbar / p := by
    calc Real.exp (M.r * T) ≤ Real.exp (Real.log (M.vbar / p)) := Real.exp_le_exp.2 hrT
      _ = M.vbar / p := Real.exp_log (by positivity)
  have hpX : p * Real.exp (M.r * T) ≤ M.vbar := by
    rw [le_div_iff₀ hp] at hX; linarith
  refine ⟨by positivity, (div_le_one hv).2 hpv, Real.one_le_exp (by positivity), ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_one hv]; exact hpX
  · intro x hx
    rw [Set.uIcc_of_le hT0] at hx
    refine ⟨by positivity, le_trans ?_ hpX⟩
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hx.2])) hp.le

lemma feas_of (M : Campaign) (hM : M.Standing) (a X : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hX : 1 ≤ X) (haX : a * X ≤ 1) : M.Feasible (M.vbar * a) (Real.log X / M.r) := by
  obtain ⟨_, _, hr, hv, _⟩ := hM
  refine ⟨by positivity, by nlinarith, div_nonneg (Real.log_nonneg hX) hr.le, ?_⟩
  apply div_le_div_of_nonneg_right _ hr.le
  apply Real.log_le_log (by linarith)
  rw [show M.vbar / (M.vbar * a) = 1 / a by field_simp, le_div_iff₀ ha]; linarith

lemma param_eq (M : Campaign) (hM : M.Standing) (p T a X : ℝ)
    (ha : p / M.vbar = a) (hX : Real.exp (M.r * T) = X) :
    p = M.vbar * a ∧ T = Real.log X / M.r := by
  obtain ⟨_, _, hr, hv, _⟩ := hM
  refine ⟨by rw [← ha]; field_simp, ?_⟩
  rw [← hX, Real.log_exp]; field_simp

lemma tri0_eq (v y : ℝ) (hv : 0 < v) (h0 : 0 ≤ y) (h1 : y ≤ v) :
    triBar0 v y = (1 - y / v) ^ 2 := by
  unfold triBar0
  rw [if_neg (not_lt.2 h0)]
  split_ifs with h
  · rfl
  · have : y = v := le_antisymm h1 (not_lt.1 h)
    subst this; simp [div_self hv.ne']

lemma tri1_eq (v y : ℝ) (hv : 0 < v) (h0 : 0 ≤ y) (h1 : y ≤ v) :
    triBar1 v y = 1 - (y / v) ^ 2 := by
  unfold triBar1
  rw [if_neg (not_lt.2 h0)]
  split_ifs with h
  · rfl
  · have : y = v := le_antisymm h1 (not_lt.1 h)
    subst this; simp [div_self hv.ne']

lemma rev_Ri (M : Campaign) (hLh : M.Lh = 0) (p T : ℝ) :
    M.revenue p T = M.k * M.Ihat * p * Real.exp (-M.k * T) *
      ∫ x in (0:ℝ)..T, Real.exp (M.k * x) * M.Fbi (p * Real.exp (M.r * x)) := by
  have hnph : M.nph p T T = 0 := by
    unfold Campaign.nph; rw [hLh]; simp
  have hsub : ∫ x in (0:ℝ)..T, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))) =
      Real.exp (-M.k * T) * ∫ x in (0:ℝ)..T, Real.exp (M.k * x) * M.Fbi (p * Real.exp (M.r * x)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => Real.exp (-M.k * (T - y)) * M.Fbi (p * Real.exp (M.r * y))) (a := 0) (b := T) T
    simp only [sub_sub_cancel, sub_self, sub_zero] at h
    rw [h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [show -M.k * (T - y) = -M.k * T + M.k * y by ring, Real.exp_add]
    ring
  unfold Campaign.revenue Campaign.ntot Campaign.npi
  rw [hnph, add_zero, hsub]
  ring

lemma rev0 (M : Campaign) (hM : M.Standing) (hkr : M.k = M.r) (hLh : M.Lh = 0)
    (hF : M.Fbi = triBar0 M.vbar) (p T : ℝ) (h : M.Feasible p T) :
    M.revenue p T = M.Ihat * M.vbar / 3 * F0 (p / M.vbar) (Real.exp (M.r * T)) := by
  obtain ⟨_, _, _, _, hpts⟩ := feas M hM p T h
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  have hp := h.1
  rw [rev_Ri M hLh, hkr, hF]
  rw [intervalIntegral.integral_congr (g := fun x =>
      Real.exp (M.r * x) * (1 - p / M.vbar * Real.exp (M.r * x)) ^ 2) (fun x hx => by
    simp only
    rw [tri0_eq _ _ hv (hpts x hx).1 (hpts x hx).2]; ring_nf)]
  rw [int0 _ _ _ hr (by positivity)]
  unfold F0
  rw [neg_mul, Real.exp_neg]
  have := Real.exp_pos (M.r * T)
  field_simp

lemma rev1 (M : Campaign) (hM : M.Standing) (hkr : M.k = M.r) (hLh : M.Lh = 0)
    (hF : M.Fbi = triBar1 M.vbar) (p T : ℝ) (h : M.Feasible p T) :
    M.revenue p T = M.Ihat * M.vbar * H1 (p / M.vbar) (Real.exp (M.r * T)) := by
  obtain ⟨_, _, _, _, hpts⟩ := feas M hM p T h
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  have hp := h.1
  rw [rev_Ri M hLh, hkr, hF]
  rw [intervalIntegral.integral_congr (g := fun x =>
      Real.exp (M.r * x) * (1 - (p / M.vbar * Real.exp (M.r * x)) ^ 2)) (fun x hx => by
    simp only
    rw [tri1_eq _ _ hv (hpts x hx).1 (hpts x hx).2]; ring_nf)]
  rw [int1 _ _ _ hr]
  unfold H1
  rw [neg_mul, Real.exp_neg]
  have := Real.exp_pos (M.r * T)
  field_simp

lemma Rh0 (M : Campaign) (hM : M.Standing) (hF : M.Fbh = triBar0 M.vbar) (p T : ℝ)
    (h : M.Feasible p T) :
    M.Rh p T = M.vbar / M.r * ((p / M.vbar) * (Real.log (Real.exp (M.r * T)) -
      2 * (p / M.vbar) * (Real.exp (M.r * T) - 1) +
      (p / M.vbar) ^ 2 * (Real.exp (M.r * T) ^ 2 - 1) / 2)) := by
  obtain ⟨_, _, _, _, hpts⟩ := feas M hM p T h
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  unfold Campaign.Rh
  rw [hF]
  rw [intervalIntegral.integral_congr (g := fun y =>
      (1 - p / M.vbar * Real.exp (M.r * y)) ^ 2) (fun x hx => by
    simp only
    rw [tri0_eq _ _ hv (hpts x hx).1 (hpts x hx).2]; ring_nf)]
  rw [int2 _ _ _ hr, Real.log_exp]
  field_simp

lemma Rh1 (M : Campaign) (hM : M.Standing) (hF : M.Fbh = triBar1 M.vbar) (p T : ℝ)
    (h : M.Feasible p T) :
    M.Rh p T = M.vbar / M.r * ((p / M.vbar) * (Real.log (Real.exp (M.r * T)) -
      (p / M.vbar) ^ 2 * (Real.exp (M.r * T) ^ 2 - 1) / 2)) := by
  obtain ⟨_, _, _, _, hpts⟩ := feas M hM p T h
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  unfold Campaign.Rh
  rw [hF]
  rw [intervalIntegral.integral_congr (g := fun y =>
      (1 - (p / M.vbar * Real.exp (M.r * y)) ^ 2)) (fun x hx => by
    simp only
    rw [tri1_eq _ _ hv (hpts x hx).1 (hpts x hx).2]; ring_nf)]
  rw [int3 _ _ _ hr, Real.log_exp]
  field_simp

/-! ### Assembly -/

lemma assemble (M : Campaign) (hM : M.Standing) (f : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hf : ∀ p T, M.Feasible p T → f p T = C * Φ (p / M.vbar) (Real.exp (M.r * T)))
    (a0 X0 : ℝ) (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (hX0 : 1 ≤ X0) (haX0 : a0 * X0 ≤ 1)
    (hcore : ∀ a X, 0 < a → a ≤ 1 → 1 ≤ X → a * X ≤ 1 →
      Φ a X ≤ Φ a0 X0 ∧ (Φ a X = Φ a0 X0 → a = a0 ∧ X = X0)) :
    IsUniqueMaxOn₂ f M.Feasible (M.vbar * a0) (Real.log X0 / M.r) := by
  have hS := feas_of M hM a0 X0 ha0 ha01 hX0 haX0
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  have hstar : f (M.vbar * a0) (Real.log X0 / M.r) = C * Φ a0 X0 := by
    rw [hf _ _ hS]
    congr 2
    · field_simp
    · rw [mul_div_cancel₀ _ hr.ne', Real.exp_log (by linarith)]
  refine ⟨hS, fun p T h => ?_, fun p T h heq => ?_⟩
  · obtain ⟨h1, h2, h3, h4, _⟩ := feas M hM p T h
    rw [hf p T h, hstar]
    exact mul_le_mul_of_nonneg_left (hcore _ _ h1 h2 h3 h4).1 hC.le
  · obtain ⟨h1, h2, h3, h4, _⟩ := feas M hM p T h
    rw [hf p T h, hstar] at heq
    have := (hcore _ _ h1 h2 h3 h4).2 (mul_left_cancel₀ hC.ne' heq)
    exact param_eq M hM p T a0 X0 this.1 this.2

lemma φb0_eq (β : ℝ) : φb0 β = Real.log (1 / β) - (3 / 2 * (β - 4 / 3) ^ 2 - 1 / 6) := by
  unfold φb0; rw [one_div, Real.log_inv]; ring

lemma core_b0 (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hc : φb0 c = 0) (a X : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hX : 1 ≤ X) (haX : a * X ≤ 1) :
    (fun a X => a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2)) a X ≤
      (fun a X => a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2)) c (1 / c) ∧
    ((fun a X => a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2)) a X =
      (fun a X => a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2)) c (1 / c) →
      a = c ∧ X = 1 / c) := by
  simp only
  have hval : ∀ b : ℝ, 0 < b →
      b * (Real.log (1 / b) - 2 * b * (1 / b - 1) + b ^ 2 * ((1 / b) ^ 2 - 1) / 2) = hb0 b := by
    intro b hb
    unfold hb0; rw [one_div, Real.log_inv]; field_simp
  rw [hval c hc0]
  obtain ⟨_, hpos, hneg⟩ := b0_signs c hc0 hc1 hc
  have hmax := umax hb0 φb0 c hc0 hc1 hb0_deriv hpos hneg
  have hX0 : 0 < X := by linarith
  -- step 1
  have hdiff : hb0 a - a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2) =
      a * (-Real.log (a * X) - 3 / 2 + 2 * (a * X) - (a * X) ^ 2 / 2) := by
    unfold hb0; rw [Real.log_mul ha.ne' hX0.ne']; ring
  have step1 : a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2) ≤ hb0 a ∧
      (a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2) = hb0 a → a * X = 1) := by
    rcases eq_or_lt_of_le haX with h | h
    · exact ⟨by rw [h] at hdiff; simp at hdiff; linarith, fun _ => h⟩
    · have := mul_pos ha (m0pos (a * X) (by positivity) h)
      exact ⟨by linarith, fun h' => by linarith⟩
  have step2 : hb0 a ≤ hb0 c ∧ (hb0 a = hb0 c → a = c) := by
    by_cases hac : a = c
    · subst hac; exact ⟨le_rfl, fun _ => rfl⟩
    · have := hmax a ha ha1 hac
      exact ⟨this.le, fun h => by linarith⟩
  refine ⟨step1.1.trans step2.1, fun heq => ?_⟩
  have e1 : hb0 a = hb0 c := le_antisymm step2.1 (heq ▸ step1.1)
  have hac := step2.2 e1
  have haX1 := step1.2 (by linarith)
  refine ⟨hac, ?_⟩
  rw [← hac]; field_simp; linarith

lemma core_b1 (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hc : φb1 c = 0) (a X : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hX : 1 ≤ X) (haX : a * X ≤ 1) :
    (fun a X => a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2)) a X ≤
      (fun a X => a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2)) c (1 / c) ∧
    ((fun a X => a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2)) a X =
      (fun a X => a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2)) c (1 / c) →
      a = c ∧ X = 1 / c) := by
  simp only
  have hval : ∀ b : ℝ, 0 < b →
      b * (Real.log (1 / b) - b ^ 2 * ((1 / b) ^ 2 - 1) / 2) = hb1 b := by
    intro b hb
    unfold hb1; rw [one_div, Real.log_inv]; field_simp
  rw [hval c hc0]
  obtain ⟨hpos, hneg⟩ := b1_signs c hc0 hc1 hc
  have hmax := umax hb1 φb1 c hc0 hc1 hb1_deriv hpos hneg
  have hX0 : 0 < X := by linarith
  have hdiff : hb1 a - a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2) =
      a * (-Real.log (a * X) - (1 - (a * X) ^ 2) / 2) := by
    unfold hb1; rw [Real.log_mul ha.ne' hX0.ne']; ring
  have step1 : a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2) ≤ hb1 a ∧
      (a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2) = hb1 a → a * X = 1) := by
    rcases eq_or_lt_of_le haX with h | h
    · exact ⟨by rw [h] at hdiff; simp at hdiff; linarith, fun _ => h⟩
    · have := mul_pos ha (m1pos (a * X) (by positivity) h)
      exact ⟨by linarith, fun h' => by linarith⟩
  have step2 : hb1 a ≤ hb1 c ∧ (hb1 a = hb1 c → a = c) := by
    by_cases hac : a = c
    · subst hac; exact ⟨le_rfl, fun _ => rfl⟩
    · have := hmax a ha ha1 hac
      exact ⟨this.le, fun h => by linarith⟩
  refine ⟨step1.1.trans step2.1, fun heq => ?_⟩
  have e1 : hb1 a = hb1 c := le_antisymm step2.1 (heq ▸ step1.1)
  have hac := step2.2 e1
  have haX1 := step1.2 (by linarith)
  refine ⟨hac, ?_⟩
  rw [← hac]; field_simp; linarith

end P7aux

open P7aux in
theorem solution (M : Campaign) (hM : M.Standing) :
    (M.k = M.r → M.Lh = 0 → M.Fbi = triBar0 M.vbar →
      IsUniqueMaxOn₂ M.revenue M.Feasible
        (M.vbar * ((x0 - Real.sqrt x0 + 1) / (x0 ^ 2 + x0 + 1))) (Real.log x0 / M.r)) ∧
    (M.k = M.r → M.Lh = 0 → M.Fbi = triBar1 M.vbar →
      IsUniqueMaxOn₂ M.revenue M.Feasible
        (M.vbar * (1 / Real.sqrt (1 + x1 + x1 ^ 2))) (Real.log x1 / M.r)) ∧
    (M.Fbh = triBar0 M.vbar →
      (∃! β : ℝ, 0 < β ∧ β < 1 ∧ Real.log (1 / β) = 3 / 2 * (β - 4 / 3) ^ 2 - 1 / 6) ∧
      ∀ β : ℝ, 0 < β → β < 1 → Real.log (1 / β) = 3 / 2 * (β - 4 / 3) ^ 2 - 1 / 6 →
        IsUniqueMaxOn₂ M.Rh M.Feasible (β * M.vbar) (Real.log (1 / β) / M.r)) ∧
    (M.Fbh = triBar1 M.vbar →
      (∃! w : ℝ, -1 < w ∧ w < 0 ∧ w * Real.exp w = -3 * Real.exp (-3)) ∧
      ∀ w : ℝ, -1 < w → w < 0 → w * Real.exp w = -3 * Real.exp (-3) →
        IsUniqueMaxOn₂ M.Rh M.Feasible
          (Real.sqrt (-w / 3) * M.vbar) (Real.log (Real.sqrt (3 / -w)) / M.r)) := by
  have hI := hM.1
  have hv := hM.2.2.2.1
  have hr := hM.2.2.1
  refine ⟨fun hkr hLh hF => ?_, fun hkr hLh hF => ?_, fun hF => ⟨?_, fun β hβ0 hβ1 hβ => ?_⟩,
    fun hF => ⟨w_exists_unique, fun w hw1 hw0 hw => ?_⟩⟩
  · -- (a), mode 0
    obtain ⟨t, ht, hx0, hP⟩ := x0_facts
    have hq : 0 < t ^ 2 + t + 1 := by positivity
    have hsq : Real.sqrt x0 = t := by rw [hx0]; exact Real.sqrt_sq (by linarith)
    have hp : (x0 - Real.sqrt x0 + 1) / (x0 ^ 2 + x0 + 1) = 1 / (t ^ 2 + t + 1) := by
      rw [hsq, hx0]
      have : 0 < t ^ 2 - t + 1 := by nlinarith
      field_simp; ring
    rw [hp, hx0]
    apply assemble M hM _ F0 (M.Ihat * M.vbar / 3) (by positivity)
      (fun p T h => rev0 M hM hkr hLh hF p T h) _ _ (by positivity)
      (by rw [div_le_one hq]; nlinarith) (by nlinarith)
      (by rw [div_mul_eq_mul_div, one_mul, div_le_one hq]; linarith)
    intro a X ha _ hX haX
    exact F0_core t ht hP a X ha hX haX
  · -- (a), mode v̄
    obtain ⟨ht, hP⟩ := x1_facts
    have hm0 : 0 < Real.sqrt (1 + x1 + x1 ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hm2 : Real.sqrt (1 + x1 + x1 ^ 2) ^ 2 = 1 + x1 + x1 ^ 2 := Real.sq_sqrt (by positivity)
    have hxm : x1 < Real.sqrt (1 + x1 + x1 ^ 2) := by nlinarith
    apply assemble M hM _ H1 (M.Ihat * M.vbar) (by positivity)
      (fun p T h => rev1 M hM hkr hLh hF p T h) _ _ (by positivity)
      (by rw [div_le_one hm0]; nlinarith) ht.le
      (by rw [div_mul_eq_mul_div, one_mul, div_le_one hm0]; linarith)
    intro a X ha _ hX haX
    exact H1_core x1 ht hP a X ha hX haX
  · -- (b), mode 0 : the root
    obtain ⟨c, hc0, hc1, hc⟩ := b0_exists
    refine ⟨c, ⟨hc0, hc1, by have := φb0_eq c; linarith⟩, fun y ⟨hy0, hy1, hy⟩ => ?_⟩
    have hyφ : φb0 y = 0 := by rw [φb0_eq]; linarith
    obtain ⟨_, hpos, hneg⟩ := b0_signs c hc0 hc1 hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hpos y hy0 h; linarith
    · have := hneg y h hy1; linarith
  · -- (b), mode 0 : the maximizer
    have hc : φb0 β = 0 := by rw [φb0_eq]; linarith
    rw [mul_comm]
    apply assemble M hM _ (fun a X => a * (Real.log X - 2 * a * (X - 1) + a ^ 2 * (X ^ 2 - 1) / 2))
      (M.vbar / M.r) (by positivity)
      (fun p T h => Rh0 M hM hF p T h) β (1 / β) hβ0 hβ1.le
      (by rw [le_div_iff₀ hβ0]; linarith) (le_of_eq (mul_one_div_cancel hβ0.ne'))
    intro a X ha ha1 hX haX
    exact core_b0 β hβ0 hβ1 hc a X ha ha1 hX haX
  · -- (b), mode v̄
    obtain ⟨hc0, hc1, hc⟩ := w_root w hw1 hw0 hw
    have hX : Real.sqrt (3 / -w) = 1 / Real.sqrt (-w / 3) := by
      rw [show 3 / -w = (-w / 3)⁻¹ by field_simp, Real.sqrt_inv, one_div]
    rw [mul_comm, hX]
    apply assemble M hM _ (fun a X => a * (Real.log X - a ^ 2 * (X ^ 2 - 1) / 2))
      (M.vbar / M.r) (by positivity)
      (fun p T h => Rh1 M hM hF p T h) _ (1 / Real.sqrt (-w / 3)) hc0 hc1.le
      (by rw [le_div_iff₀ hc0]; linarith) (le_of_eq (mul_one_div_cancel hc0.ne'))
    intro a X ha ha1 hX haX
    exact core_b1 _ hc0 hc1 hc a X ha ha1 hX haX
