-- Prove2me | solution 1 for BayesBAI.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T08:10:10.859763+00:00
-- url     : https://prove2.me/submissions/064ca059-abc0-461c-9a04-6eae65764573

import Mathlib
import Definitions.Def_BayesBAI_KLSetting
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

open BayesBAI RegretBandits.Stochastic Finset

lemma cubic' (x : ℝ) (h1 : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤ 2 * |x| ^ 3 ∧ |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * |x| ^ 3 := by
  have hb : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg x) 3]
  constructor
  · have := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 2
    rw [abs_neg] at this
    refine le_trans (le_of_eq ?_) (this.trans hb); congr 1; simp [sum_range_succ]; ring
  · have := Real.abs_log_sub_add_sum_range_le (x := x) (by linarith) 2
    refine le_trans (le_of_eq ?_) (this.trans hb); congr 1; simp [sum_range_succ]; ring

lemma approx (ε p q : ℝ) (hε : 0 < ε) (hp1 : ε / 2 ≤ p) (hp2 : p ≤ 1 - ε / 2) (hq : |q - p| ≤ ε / 4) :
    |klBern p q - (q - p) ^ 2 / (2 * p * (1 - p))| ≤ 16 * |q - p| ^ 3 / ε ^ 2 := by
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 - p := by linarith
  set δ := q - p with hδ
  have hδa := abs_le.mp hq
  have hq0 : 0 < q := by linarith
  have h1q : 0 < 1 - q := by linarith
  set a := δ / p with ha
  set b := δ / (1 - p) with hb
  have haa : |a| = |δ| / p := by rw [ha, abs_div, abs_of_pos hp0]
  have hbb : |b| = |δ| / (1 - p) := by rw [hb, abs_div, abs_of_pos h1p]
  have ha1 : |a| ≤ 1 / 2 := by rw [haa, div_le_iff₀ hp0]; linarith
  have hb1 : |b| ≤ 1 / 2 := by rw [hbb, div_le_iff₀ h1p]; linarith
  obtain ⟨hE1, _⟩ := cubic' a ha1
  obtain ⟨_, hE2⟩ := cubic' b hb1
  have hlog1 : Real.log (p / q) = -Real.log (1 + a) := by
    rw [← Real.log_inv]; congr 1
    rw [ha, hδ, show 1 + (q - p) / p = q / p by field_simp [hp0.ne']; ring, inv_div]
  have hlog2 : Real.log ((1 - p) / (1 - q)) = -Real.log (1 - b) := by
    rw [← Real.log_inv]; congr 1
    rw [hb, hδ, show 1 - (q - p) / (1 - p) = (1 - q) / (1 - p) by field_simp [h1p.ne']; ring, inv_div]
  have hkey : klBern p q - δ ^ 2 / (2 * p * (1 - p)) =
      -p * (Real.log (1 + a) - a + a ^ 2 / 2) - (1 - p) * (Real.log (1 - b) + b + b ^ 2 / 2) := by
    unfold klBern; rw [hlog1, hlog2, ha, hb]; field_simp; ring
  rw [hkey]
  have e1 : p * (2 * |a| ^ 3) = 2 * |δ| ^ 3 / p ^ 2 := by rw [haa]; field_simp
  have e2 : (1 - p) * (2 * |b| ^ 3) = 2 * |δ| ^ 3 / (1 - p) ^ 2 := by rw [hbb]; field_simp
  have hε2 : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
  have f1 : 2 * |δ| ^ 3 / p ^ 2 ≤ 8 * |δ| ^ 3 / ε ^ 2 := by
    calc 2 * |δ| ^ 3 / p ^ 2 ≤ 2 * |δ| ^ 3 / (ε / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hp1 2)
      _ = 8 * |δ| ^ 3 / ε ^ 2 := by rw [hε2]; field_simp; ring
  have f2 : 2 * |δ| ^ 3 / (1 - p) ^ 2 ≤ 8 * |δ| ^ 3 / ε ^ 2 := by
    calc 2 * |δ| ^ 3 / (1 - p) ^ 2 ≤ 2 * |δ| ^ 3 / (ε / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
      _ = 8 * |δ| ^ 3 / ε ^ 2 := by rw [hε2]; field_simp; ring
  calc |-p * (Real.log (1 + a) - a + a ^ 2 / 2) - (1 - p) * (Real.log (1 - b) + b + b ^ 2 / 2)|
      ≤ |-p * (Real.log (1 + a) - a + a ^ 2 / 2)| + |(1 - p) * (Real.log (1 - b) + b + b ^ 2 / 2)| :=
        abs_sub _ _
    _ = p * |Real.log (1 + a) - a + a ^ 2 / 2| + (1 - p) * |Real.log (1 - b) + b + b ^ 2 / 2| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hp0, abs_of_pos h1p]
    _ ≤ p * (2 * |a| ^ 3) + (1 - p) * (2 * |b| ^ 3) := by gcongr
    _ ≤ 16 * |δ| ^ 3 / ε ^ 2 := by rw [e1, e2]; have : 16 * |δ| ^ 3 / ε ^ 2 = 8 * |δ| ^ 3 / ε ^ 2 + 8 * |δ| ^ 3 / ε ^ 2 := by ring
                                   linarith

lemma compare (ε p p' d : ℝ) (hε : 0 < ε) (hp1 : ε / 2 ≤ p) (hp2 : p ≤ 1 - ε / 2)
    (hq1 : ε / 2 ≤ p') (hq2 : p' ≤ 1 - ε / 2) :
    |d ^ 2 / (2 * p * (1 - p)) - d ^ 2 / (2 * p' * (1 - p'))| ≤ 8 * d ^ 2 * |p - p'| / ε ^ 2 := by
  have hX : ε / 4 ≤ p * (1 - p) := by nlinarith
  have hY : ε / 4 ≤ p' * (1 - p') := by nlinarith
  have hX0 : 0 < p * (1 - p) := by linarith
  have hY0 : 0 < p' * (1 - p') := by linarith
  have hp0 : p ≠ 0 := by intro h; rw [h] at hX0; simp at hX0
  have h1p : 1 - p ≠ 0 := by intro h; rw [h] at hX0; simp at hX0
  have hq0 : p' ≠ 0 := by intro h; rw [h] at hY0; simp at hY0
  have h1q : 1 - p' ≠ 0 := by intro h; rw [h] at hY0; simp at hY0
  have e : d ^ 2 / (2 * p * (1 - p)) - d ^ 2 / (2 * p' * (1 - p')) =
      d ^ 2 * ((p' - p) * (1 - p - p')) / (2 * (p * (1 - p)) * (p' * (1 - p'))) := by
    field_simp; ring
  have hden : 0 < 2 * (p * (1 - p)) * (p' * (1 - p')) := mul_pos (mul_pos two_pos hX0) hY0
  rw [e, abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg d), abs_sub_comm p' p,
    div_le_div_iff₀ hden (by positivity)]
  have hs : |1 - p - p'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hXY : ε ^ 2 / 16 ≤ (p * (1 - p)) * (p' * (1 - p')) := by
    have := mul_le_mul hX hY (by positivity) hX0.le; nlinarith
  have hd := sq_nonneg d
  have hpp := abs_nonneg (p - p')
  calc d ^ 2 * (|p - p'| * |1 - p - p'|) * ε ^ 2 ≤ d ^ 2 * (|p - p'| * 1) * ε ^ 2 := by gcongr
    _ = 16 * (d ^ 2 * |p - p'|) * (ε ^ 2 / 16) := by ring
    _ ≤ 16 * (d ^ 2 * |p - p'|) * ((p * (1 - p)) * (p' * (1 - p'))) := by gcongr
    _ = 8 * d ^ 2 * |p - p'| * (2 * (p * (1 - p)) * (p' * (1 - p'))) := by ring

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ {T l u h : ℝ}, KLSetting T l u h →
      |klBern ((l + u) / 2) u - klBern l ((l + u) / 2)| ≤ C * h ^ 3 * T ^ ((1 : ℝ) / 3) ∧
      |klBern ((l + u) / 2) u - klBern u ((l + u) / 2)| ≤ C * h ^ 3 * T ^ ((1 : ℝ) / 3) := by
  refine ⟨8, by norm_num, fun {T l u h} hs => ?_⟩
  obtain ⟨hT, _, hh, hl1, hl2, hlu, hu⟩ := hs
  set ε := T ^ (-(1 / 6) : ℝ) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hT _
  have hε2 : T ^ ((1 : ℝ) / 3) = 1 / ε ^ 2 := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, one_div (_ ^ _), ← Real.rpow_neg hT.le]
    norm_num
  set m := (l + u) / 2 with hm
  set d := (u - l) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hdh : d ≤ h / 2 := by rw [hd]; linarith
  have hdε : d ≤ ε / 4 := by linarith
  have hum : u - m = d := by rw [hm, hd]; ring
  have hml : m - l = d := by rw [hm, hd]; ring
  have hmu : m - u = -d := by rw [hm, hd]; ring
  have Pl1 : ε / 2 ≤ l := by linarith
  have Pl2 : l ≤ 1 - ε / 2 := by linarith
  have Pm1 : ε / 2 ≤ m := by rw [hm]; linarith
  have Pm2 : m ≤ 1 - ε / 2 := by rw [hm]; linarith
  have Pu1 : ε / 2 ≤ u := by linarith
  have Pu2 : u ≤ 1 - ε / 2 := by linarith
  have A1 := approx ε m u hε0 Pm1 Pm2 (by rw [hum, abs_of_pos hd0]; exact hdε)
  have A2 := approx ε l m hε0 Pl1 Pl2 (by rw [hml, abs_of_pos hd0]; exact hdε)
  have A3 := approx ε u m hε0 Pu1 Pu2 (by rw [hmu, abs_neg, abs_of_pos hd0]; exact hdε)
  rw [hum, abs_of_pos hd0] at A1
  rw [hml, abs_of_pos hd0] at A2
  rw [hmu, abs_neg, abs_of_pos hd0, neg_sq] at A3
  have C1 := compare ε m l d hε0 Pm1 Pm2 Pl1 Pl2
  have C2 := compare ε m u d hε0 Pm1 Pm2 Pu1 Pu2
  rw [hml, abs_of_pos hd0] at C1
  rw [hmu, abs_neg, abs_of_pos hd0] at C2
  have hd3 : d ^ 3 ≤ (h / 2) ^ 3 := pow_le_pow_left₀ hd0.le hdh 3
  have K : 16 * d ^ 3 / ε ^ 2 + 16 * d ^ 3 / ε ^ 2 + 8 * d ^ 2 * d / ε ^ 2 ≤ 8 * h ^ 3 * (1 / ε ^ 2) := by
    rw [show 16 * d ^ 3 / ε ^ 2 + 16 * d ^ 3 / ε ^ 2 + 8 * d ^ 2 * d / ε ^ 2 = (40 * d ^ 3) * (1 / ε ^ 2) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : 0 ≤ h := by linarith
    nlinarith [pow_nonneg this 3]
  rw [hε2]
  have a1 := abs_le.mp A1
  have a2 := abs_le.mp A2
  have a3 := abs_le.mp A3
  have c1 := abs_le.mp C1
  have c2 := abs_le.mp C2
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
