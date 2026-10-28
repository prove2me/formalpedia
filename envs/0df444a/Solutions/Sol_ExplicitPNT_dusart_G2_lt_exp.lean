-- Prove2me | solution 1 for ExplicitPNT.dusart_G2_lt_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:55:18.173653+00:00
-- url     : https://prove2.me/submissions/7477e7ca-5010-41e6-8407-a4045d1f808a

import Mathlib

namespace PNT_faac

lemma log2pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.pi_lt_d2]

lemma one_lt_log2pi : 1 < Real.log (2 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h := Real.exp_one_lt_d9
  nlinarith [Real.pi_gt_three]

lemma s_small (X : ℝ) (hX : 836/100 < X) : Real.sqrt X * Real.exp (-X) ≤ 3/100 := by
  have hX0 : 0 < X := by linarith
  have h5 := Real.pow_div_factorial_le_exp X hX0.le 5
  norm_num [Nat.factorial] at h5
  have hsq : Real.sqrt X ≤ X := by
    nlinarith [Real.sq_sqrt hX0.le, Real.sqrt_nonneg X]
  have hX2 : X^2 ≥ 69 := by nlinarith
  have hX4 : X^4 ≥ 4000 := by nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos X)]
  nlinarith


lemma P_le_one (ν : ℝ) (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1) :
    ν ^ 6 / (2 * ν ^ 2 - 1) ≤ 1 := by
  have hν2 : 9409/10000 < ν^2 := by nlinarith
  have hν21 : ν^2 ≤ 1 := by nlinarith
  rw [div_le_one (by nlinarith)]
  have hu : ν^6 = (ν^2)^3 := by ring
  have h1 : 0 ≤ (ν^2)^2 + ν^2 - 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hν21) h1]

lemma G0_le_one (X ν L : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1) (hL1 : 1 < L) (hL2 : L < 2) :
    ν ^ 6 / (2 * ν ^ 2 - 1) * (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)) ≤ 1 := by
  have hm : 8 < X * ν := by nlinarith
  have hXν : 0 < X * ν := by linarith
  have hF1a : 0 ≤ (L - 1/2)/(X*ν) := div_nonneg (by linarith) hXν.le
  have hF1b : (L - 1/2)/(X*ν) ≤ 1 := by rw [div_le_one hXν]; linarith
  have hF2a : 0 ≤ L/(X*ν) := div_nonneg (by linarith) hXν.le
  have hF2b : L/(X*ν) ≤ 1 := by rw [div_le_one hXν]; linarith
  have f1 : 0 ≤ 1 - (L - 1 / 2) / (X * ν) := by linarith
  have f2 : 1 - (L - 1 / 2) / (X * ν) ≤ 1 := by linarith
  have f3 : 0 ≤ 1 - L / (X * ν) := by linarith
  have f4 : 1 - L / (X * ν) ≤ 1 := by linarith
  exact mul_le_one₀ (mul_le_one₀ (P_le_one ν hν₀ hν₁) f1 f2) f3 f4

lemma sqrt2pi_le : Real.sqrt (2 / Real.pi) ≤ 8/10 := by
  have hπ := Real.pi_gt_d2
  have h1 : 2 / Real.pi ≤ 64/100 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 / Real.pi by positivity),
    Real.sqrt_nonneg (2 / Real.pi)]

lemma delta_bound (X ν L Y s : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1) (hL1 : 1 < L) (hL2 : L < 2)
    (hY : 0 ≤ Y) (hs : 0 ≤ s) :
    0 ≤ Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) * (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)))) *
      Real.exp (-Y / 2) * s ∧
    Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) * (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)))) *
      Real.exp (-Y / 2) * s ≤ 8/10 * s := by
  have hb := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr (G0_le_one X ν L hX hν₀ hν₁ hL1 hL2))
  have hc : Real.exp (-Y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha := sqrt2pi_le
  have hb0 := Real.sqrt_nonneg (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) * (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν))))
  generalize Real.sqrt (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) * (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)))) = b at hb hb0 ⊢
  have ha0 := Real.sqrt_nonneg (2 / Real.pi)
  have hc0 := (Real.exp_pos (-Y / 2)).le
  generalize Real.sqrt (2 / Real.pi) = a at ha ha0 ⊢
  generalize Real.exp (-Y / 2) = c at hc hc0 ⊢
  constructor
  · positivity
  · have habc : a * b * c ≤ 8/10 := by
      calc a * b * c ≤ 8/10 * 1 * 1 := by gcongr
        _ = 8/10 := by norm_num
    exact mul_le_mul_of_nonneg_right habc hs

lemma K_bound (X ν L : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1) (hL1 : 1 < L) (hL2 : L < 2) :
    Real.sqrt ((ν ^ 2 * (ν - L / X)) ^ 3 /
      (ν ^ 2 / (2 * ν ^ 2 - 1) * (ν + (1 - 2 * L) / (2 * X)))) ≤ 11252/10000 := by
  have hX0 : 0 < X := by linarith
  have hν2 : 9409/10000 < ν^2 := by nlinarith
  have hν21 : ν^2 ≤ 1 := by nlinarith
  have hLX : L / X < 1/4 := by rw [div_lt_iff₀ hX0]; linarith
  have hLX0 : 0 ≤ L / X := div_nonneg (by linarith) hX0.le
  have hA0 : 0 < ν ^ 2 * (ν - L / X) := by apply mul_pos (by positivity); linarith
  have hA1 : ν ^ 2 * (ν - L / X) ≤ 1 := by nlinarith
  have hR : 1 ≤ ν ^ 2 / (2 * ν ^ 2 - 1) := by rw [le_div_iff₀ (by nlinarith)]; nlinarith
  have hS0 : -18/100 ≤ (1 - 2 * L) / (2 * X) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  generalize ν ^ 2 / (2 * ν ^ 2 - 1) = R at hR ⊢
  generalize (1 - 2 * L) / (2 * X) = S at hS0 ⊢
  generalize ν ^ 2 * (ν - L / X) = A at hA0 hA1 ⊢
  have hB : 79/100 ≤ R * (ν + S) := by nlinarith
  have hA3 : A ^ 3 ≤ 1 := pow_le_one₀ hA0.le hA1
  have hAB : A ^ 3 / (R * (ν + S)) ≤ 12659/10000 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hK2 := Real.sq_sqrt (div_nonneg (pow_nonneg hA0.le 3) (show 0 ≤ R * (ν + S) by linarith))
  have hK0 := Real.sqrt_nonneg (A ^ 3 / (R * (ν + S)))
  generalize Real.sqrt (A ^ 3 / (R * (ν + S))) = K at hK2 hK0 ⊢
  nlinarith

lemma r_bound (X ν K Y : ℝ) (hX : (836 / 100 : ℝ) < X) (hK0 : 0 ≤ K) (hK1 : K ≤ 11252/10000)
    (hY : 0 ≤ Y)
    (hk : X / (2 * Real.pi) * K * Real.exp (-(2 * X * (1 - ν))) * Real.exp (-Y) = 1) :
    2 * Real.pi / Real.exp (ν * X) ≤ 267/100 * (Real.sqrt X * Real.exp (-X)) := by
  have hX0 : 0 < X := by linarith
  have hπ2 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hr0 : 0 ≤ 2 * Real.pi / Real.exp (ν * X) := by positivity
  have hs0 : 0 ≤ Real.sqrt X * Real.exp (-X) := by positivity
  have hr2 : (2 * Real.pi / Real.exp (ν * X)) ^ 2
      = (2 * Real.pi) ^ 2 * (Real.exp (-2 * X) * Real.exp (2 * X * (1 - ν))) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_pow, sq (Real.exp _),
      ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  have hs2 : (Real.sqrt X * Real.exp (-X)) ^ 2 = X * Real.exp (-2 * X) := by
    rw [mul_pow, Real.sq_sqrt hX0.le, sq (Real.exp _), ← Real.exp_add]; ring_nf
  have heY : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 : 0 < Real.exp (-2 * X) := Real.exp_pos _
  rw [Real.exp_neg (2 * X * (1 - ν))] at hk
  have hE0 := Real.exp_pos (2 * X * (1 - ν))
  generalize Real.exp (2 * X * (1 - ν)) = E at hk hr2 hE0
  generalize 2 * Real.pi / Real.exp (ν * X) = r at hr0 hr2 ⊢
  generalize Real.sqrt X * Real.exp (-X) = s at hs0 hs2 ⊢
  generalize Real.exp (-2 * X) = e at he2 hr2 hs2
  have hw0 := (Real.exp_pos (-Y)).le
  generalize Real.exp (-Y) = w at heY hk hw0
  have h1 : 2 * Real.pi * E = X * K * w := by
    calc 2 * Real.pi * E = 2 * Real.pi * E * (X / (2 * Real.pi) * K * E⁻¹ * w) := by
          rw [hk, mul_one]
      _ = X * K * w := by field_simp
  have hXK : 0 ≤ X * K := by positivity
  have h2 : 2 * Real.pi * E ≤ X * K := by rw [h1]; nlinarith
  have h3 : 2 * Real.pi * K ≤ 71/10 := by nlinarith
  have h4 : r ^ 2 ≤ 71/10 * s ^ 2 := by
    rw [hr2, hs2]
    have e1 : (2 * Real.pi) ^ 2 * (e * E) = (2 * Real.pi * e) * (2 * Real.pi * E) := by ring
    rw [e1]
    have e2 : (2 * Real.pi * e) * (2 * Real.pi * E) ≤ (2 * Real.pi * e) * (X * K) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e3 : (2 * Real.pi * e) * (X * K) = (2 * Real.pi * K) * (X * e) := by ring
    have e4 : 0 ≤ X * e := by positivity
    nlinarith
  nlinarith

lemma frac_bound (m L : ℝ) (hm1 : 81/10 ≤ m) (hL2 : L < 2) :
    (137 / 1000 * m + 443 / 1000) / (m * (m - L)) ≤ 315/10000 := by
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ m - 81/10 by linarith)
    (show (0:ℝ) ≤ m - L - 61/10 by linarith)]

lemma assemble (δ Q s : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 8/10 * s) (hs0 : 0 < s) (hs1 : s ≤ 3/100)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 9/100 * s) :
    ((1 + δ) ^ 3 + 1) ^ 2 / 2 ^ 2 * (1 + Q) < Real.exp (264 / 100 * s) := by
  have hG' : ((1 + δ) ^ 3 + 1) ^ 2 / 2 ^ 2 * (1 + Q)
      = (1 + δ * (3 + 3 * δ + δ ^ 2) / 2) ^ 2 * (1 + Q) := by ring
  have hδ2 : δ ≤ 3/100 := by nlinarith
  have h3 : 3 + 3 * δ + δ ^ 2 ≤ 31/10 := by nlinarith
  have hp : δ * (3 + 3 * δ + δ ^ 2) ≤ (8/10 * s) * (31/10) :=
    mul_le_mul hδ1 h3 (by positivity) (by positivity)
  rw [hG']
  generalize hx : δ * (3 + 3 * δ + δ ^ 2) / 2 = x
  have hx0 : 0 ≤ x := by rw [← hx]; positivity
  have hx1 : 2 * x ≤ 25/10 * s := by rw [← hx]; nlinarith
  have hex : (1 + x) ^ 2 ≤ Real.exp (2 * x) := by
    have h := Real.add_one_le_exp x
    have : Real.exp (2 * x) = Real.exp x ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have heq : 1 + Q ≤ Real.exp Q := by
    have := Real.add_one_le_exp Q; linarith
  calc (1 + x) ^ 2 * (1 + Q)
      ≤ Real.exp (2 * x) * Real.exp Q :=
        mul_le_mul hex heq (by linarith) (Real.exp_pos _).le
    _ = Real.exp (2 * x + Q) := by rw [Real.exp_add]
    _ < Real.exp (264 / 100 * s) := by
        apply Real.exp_lt_exp.mpr; linarith

end PNT_faac

theorem solution (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν₀ : (97 / 100 : ℝ) < ν) (hν₁ : ν < 1)
    (hk : X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) = 1) :
    let δ := Real.sqrt (2 / Real.pi) *
      Real.sqrt (Real.sqrt
        (ν ^ 6 / (2 * ν ^ 2 - 1) *
          (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
          (1 - Real.log (2 * Real.pi) / (X * ν)))) *
      Real.exp (-(X * (1 - ν) ^ 2 / ν) / 2) * Real.sqrt X * Real.exp (-X)
    let T₂ := Real.exp (ν * X)
    let q := ((137 / 1000 : ℝ) * Real.log T₂ + 443 / 1000) /
      (T₂ * Real.log T₂ * Real.log (T₂ / (2 * Real.pi)))
    let G₂ := ((1 + δ) ^ 3 + 1) ^ 2 / 2 ^ 2 * (1 + 2 * Real.pi * q)
    G₂ < Real.exp ((264 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) := by
  dsimp only
  have hX0 : 0 < X := by linarith
  have hπ0 := Real.pi_pos
  rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  rw [mul_assoc (264 / 100 : ℝ) (Real.sqrt X) (Real.exp (-X))]
  rw [mul_assoc _ (Real.sqrt X) (Real.exp (-X))]
  have hL1 := PNT_faac.one_lt_log2pi
  have hL2 := PNT_faac.log2pi_lt_two
  have hs1 := PNT_faac.s_small X hX
  have hs0 : 0 < Real.sqrt X * Real.exp (-X) := by positivity
  generalize Real.log (2 * Real.pi) = L at hL1 hL2 hk ⊢
  have hY : 0 ≤ X * (1 - ν) ^ 2 / ν := by
    have : 0 < ν := by linarith
    positivity
  obtain ⟨hδ0, hδ1⟩ := PNT_faac.delta_bound X ν L (X * (1 - ν) ^ 2 / ν)
    (Real.sqrt X * Real.exp (-X)) hX hν₀ hν₁ hL1 hL2 hY hs0.le
  have hK1 := PNT_faac.K_bound X ν L hX hν₀ hν₁ hL1 hL2
  have hr := PNT_faac.r_bound X ν _ _ hX (Real.sqrt_nonneg _) hK1 hY hk
  have hm1 : 81/10 ≤ ν * X := by nlinarith
  have hfr := PNT_faac.frac_bound (ν * X) L hm1 hL2
  have hfr0 : 0 ≤ (137 / 1000 * (ν * X) + 443 / 1000) / ((ν * X) * ((ν * X) - L)) := by
    apply div_nonneg (by linarith); nlinarith
  have hr0 : 0 ≤ 2 * Real.pi / Real.exp (ν * X) := by positivity
  have hq : 2 * Real.pi * ((137 / 1000 * (ν * X) + 443 / 1000) /
      (Real.exp (ν * X) * (ν * X) * (ν * X - L)))
      = 2 * Real.pi / Real.exp (ν * X) *
        ((137 / 1000 * (ν * X) + 443 / 1000) / ((ν * X) * ((ν * X) - L))) := by
    have : 0 < Real.exp (ν * X) := Real.exp_pos _
    rw [div_mul_div_comm, mul_div_assoc', mul_assoc (Real.exp (ν * X))]
  have hQ0 : 0 ≤ 2 * Real.pi * ((137 / 1000 * (ν * X) + 443 / 1000) /
      (Real.exp (ν * X) * (ν * X) * (ν * X - L))) := by rw [hq]; positivity
  have hQ1 : 2 * Real.pi * ((137 / 1000 * (ν * X) + 443 / 1000) /
      (Real.exp (ν * X) * (ν * X) * (ν * X - L))) ≤ 9/100 * (Real.sqrt X * Real.exp (-X)) := by
    rw [hq]
    calc _ ≤ (267/100 * (Real.sqrt X * Real.exp (-X))) * (315/10000) :=
          mul_le_mul hr hfr hfr0 (by positivity)
      _ ≤ _ := by nlinarith
  exact PNT_faac.assemble _ _ _ hδ0 hδ1 hs0 hs1 hQ0 hQ1
