-- Prove2me | solution 1 for BBDisclosure.Total.proposition_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:06:18.11048+00:00
-- url     : https://prove2.me/submissions/a5c6e723-f7a0-49fa-8d9a-43d5c84dbf3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game
import Theorems.Thm_BBDisclosure_Total_equation_9
import Theorems.Thm_BBDisclosure_Total_equation_17

namespace BBDP2Aux

noncomputable def F (c : ℝ) : ℝ :=
  2 + 0 * c - 1 * ((5 + 54 * c) / Real.sqrt (1 + 12 * c))
    - (-5 - 162 * c) / Real.sqrt (1 + 108 * c)
    + (-2 + 0 * c) / Real.sqrt (1 + 27 * c)

lemma lb_gen {N s L slo shi Nlo : ℝ} (hs : 0 < slo) (h1 : slo ≤ s) (h2 : s ≤ shi)
    (hN : Nlo ≤ N) (hA : L * slo ≤ Nlo) (hB : L * shi ≤ Nlo) : L ≤ N / s := by
  rw [le_div_iff₀ (by linarith)]
  rcases le_total 0 L with hL | hL
  · nlinarith [mul_le_mul_of_nonneg_left h2 hL]
  · nlinarith [mul_le_mul_of_nonpos_left h1 hL]

lemma ub_gen {N s U slo shi Nhi : ℝ} (hs : 0 < slo) (h1 : slo ≤ s) (h2 : s ≤ shi)
    (hN : N ≤ Nhi) (hA : Nhi ≤ U * slo) (hB : Nhi ≤ U * shi) : N / s ≤ U := by
  rw [div_le_iff₀ (by linarith)]
  rcases le_total 0 U with hU | hU
  · nlinarith [mul_le_mul_of_nonneg_left h1 hU]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hU]

lemma sqrt_ge {x y lo : ℝ} (h0 : 0 ≤ lo) (h : lo ^ 2 ≤ x) (hxy : x ≤ y) : lo ≤ Real.sqrt y :=
  Real.le_sqrt_of_sq_le (le_trans h hxy)

lemma sqrt_le' {x y hi : ℝ} (h0 : 0 ≤ hi) (h : y ≤ hi ^ 2) (hxy : x ≤ y) : Real.sqrt x ≤ hi := by
  calc Real.sqrt x ≤ Real.sqrt (hi ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = hi := Real.sqrt_sq h0


lemma box_neg (x0 x1 alo ahi blo bhi dlo dhi L1 L3 U2 : ℝ)
    (h0 : 0 ≤ x0)
    (ha0 : 0 < alo) (ha1 : alo ^ 2 ≤ 1 + 12 * x0) (ha2 : 1 + 12 * x1 ≤ ahi ^ 2) (ha3 : 0 ≤ ahi)
    (hb0 : 0 < blo) (hb1 : blo ^ 2 ≤ 1 + 27 * x0) (hb2 : 1 + 27 * x1 ≤ bhi ^ 2) (hb3 : 0 ≤ bhi)
    (hd0 : 0 < dlo) (hd1 : dlo ^ 2 ≤ 1 + 108 * x0) (hd2 : 1 + 108 * x1 ≤ dhi ^ 2) (hd3 : 0 ≤ dhi)
    (h1a : L1 * alo ≤ 5 + 54 * x0) (h1b : L1 * ahi ≤ 5 + 54 * x0)
    (h3a : L3 * dlo ≤ -5 - 162 * x1) (h3b : L3 * dhi ≤ -5 - 162 * x1)
    (h2a : -2 + 0 * x0 ≤ U2 * blo) (h2b : -2 + 0 * x0 ≤ U2 * bhi)
    (hsum : 2 + 0 * x1 - 1 * L1 - L3 + U2 < 0) :
    ∀ c ∈ Set.Icc x0 x1, F c < 0 := by
  rintro c ⟨hc0, hc1⟩
  have e1 := lb_gen ha0 (show alo ≤ Real.sqrt (1 + 12 * c) from sqrt_ge ha0.le ha1 (by linarith)) (show Real.sqrt (1 + 12 * c) ≤ ahi from sqrt_le' ha3 ha2 (by linarith))
    (show 5 + 54 * x0 ≤ 5 + 54 * c by nlinarith) h1a h1b
  have e3 := lb_gen hd0 (show dlo ≤ Real.sqrt (1 + 108 * c) from sqrt_ge hd0.le hd1 (by linarith)) (show Real.sqrt (1 + 108 * c) ≤ dhi from sqrt_le' hd3 hd2 (by linarith))
    (show -5 - 162 * x1 ≤ -5 - 162 * c by nlinarith) h3a h3b
  have e2 := ub_gen hb0 (show blo ≤ Real.sqrt (1 + 27 * c) from sqrt_ge hb0.le hb1 (by linarith)) (show Real.sqrt (1 + 27 * c) ≤ bhi from sqrt_le' hb3 hb2 (by linarith))
    (show -2 + 0 * c ≤ -2 + 0 * x0 by nlinarith) h2a h2b
  unfold F
  linarith

lemma box_pos (x0 x1 alo ahi blo bhi dlo dhi U1 U3 L2 : ℝ)
    (h0 : 0 ≤ x0)
    (ha0 : 0 < alo) (ha1 : alo ^ 2 ≤ 1 + 12 * x0) (ha2 : 1 + 12 * x1 ≤ ahi ^ 2) (ha3 : 0 ≤ ahi)
    (hb0 : 0 < blo) (hb1 : blo ^ 2 ≤ 1 + 27 * x0) (hb2 : 1 + 27 * x1 ≤ bhi ^ 2) (hb3 : 0 ≤ bhi)
    (hd0 : 0 < dlo) (hd1 : dlo ^ 2 ≤ 1 + 108 * x0) (hd2 : 1 + 108 * x1 ≤ dhi ^ 2) (hd3 : 0 ≤ dhi)
    (h1a : 5 + 54 * x1 ≤ U1 * alo) (h1b : 5 + 54 * x1 ≤ U1 * ahi)
    (h3a : -5 - 162 * x0 ≤ U3 * dlo) (h3b : -5 - 162 * x0 ≤ U3 * dhi)
    (h2a : L2 * blo ≤ -2 + 0 * x1) (h2b : L2 * bhi ≤ -2 + 0 * x1)
    (hsum : 0 < 2 + 0 * x0 - 1 * U1 - U3 + L2) :
    ∀ c ∈ Set.Icc x0 x1, 0 < F c := by
  rintro c ⟨hc0, hc1⟩
  have e1 := ub_gen ha0 (show alo ≤ Real.sqrt (1 + 12 * c) from sqrt_ge ha0.le ha1 (by linarith)) (show Real.sqrt (1 + 12 * c) ≤ ahi from sqrt_le' ha3 ha2 (by linarith))
    (show 5 + 54 * c ≤ 5 + 54 * x1 by nlinarith) h1a h1b
  have e3 := ub_gen hd0 (show dlo ≤ Real.sqrt (1 + 108 * c) from sqrt_ge hd0.le hd1 (by linarith)) (show Real.sqrt (1 + 108 * c) ≤ dhi from sqrt_le' hd3 hd2 (by linarith))
    (show -5 - 162 * c ≤ -5 - 162 * x0 by nlinarith) h3a h3b
  have e2 := lb_gen hb0 (show blo ≤ Real.sqrt (1 + 27 * c) from sqrt_ge hb0.le hb1 (by linarith)) (show Real.sqrt (1 + 27 * c) ≤ bhi from sqrt_le' hb3 hb2 (by linarith))
    (show -2 + 0 * x1 ≤ -2 + 0 * c by nlinarith) h2a h2b
  unfold F
  linarith

lemma cover_join {P : ℝ → Prop} {a b d : ℝ} (h1 : ∀ c ∈ Set.Icc a b, P c) (h2 : ∀ c ∈ Set.Icc b d, P c) :
    ∀ c ∈ Set.Icc a d, P c := by
  rintro c ⟨hc0, hc1⟩
  rcases le_total c b with h | h
  · exact h1 c ⟨hc0, h⟩
  · exact h2 c ⟨h, hc1⟩


lemma term_deriv (n0 n1 n2 k x : ℝ) (hx : 0 < 1 + k * x) :
    HasDerivAt (fun c => (n0 + n1 * c + n2 * c ^ 2) / Real.sqrt (1 + k * c))
      (((n1 + 2 * n2 * x) * (1 + k * x) - k / 2 * (n0 + n1 * x + n2 * x ^ 2)) /
        (Real.sqrt (1 + k * x)) ^ 3) x := by
  have h1 : HasDerivAt (fun c : ℝ => 1 + k * c) k x := by
    simpa using ((hasDerivAt_id x).const_mul k).const_add 1
  have hs := h1.sqrt hx.ne'
  have hN : HasDerivAt (fun c : ℝ => n0 + n1 * c + n2 * c ^ 2) (n1 + 2 * n2 * x) x := by
    have := ((hasDerivAt_const x n0).add ((hasDerivAt_id' x).const_mul n1)).add
      ((hasDerivAt_pow 2 x).const_mul n2)
    exact this.congr_deriv (by norm_num; ring)
  have hpos : 0 < Real.sqrt (1 + k * x) := Real.sqrt_pos.2 hx
  refine (hN.div hs hpos.ne').congr_deriv ?_
  have hsq : Real.sqrt (1 + k * x) ^ 2 = 1 + k * x := Real.sq_sqrt hx.le
  set s := Real.sqrt (1 + k * x) with hsdef
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have e : 1 + k * x = s ^ 2 := hsq.symm
  rw [e]
  field_simp

lemma taylor_lo {x s : ℝ} (hx : 0 ≤ x) (hs : s = Real.sqrt (1 + x)) :
    s * (1 - x / 2 + 3 / 8 * x ^ 2 - 5 / 16 * x ^ 3) ≤ 1 := by
  have h1 : 1 ≤ s := by rw [hs]; exact Real.le_sqrt_of_sq_le (by linarith)
  have h2 : s ^ 2 = 1 + x := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hx' : x = s ^ 2 - 1 := by linarith
  subst hx'
  have : s * (1 - (s ^ 2 - 1) / 2 + 3 / 8 * (s ^ 2 - 1) ^ 2 - 5 / 16 * (s ^ 2 - 1) ^ 3) - 1
      = -((s - 1) ^ 4 * (5 * s ^ 3 + 20 * s ^ 2 + 29 * s + 16)) / 16 := by ring
  have h3 : 0 ≤ (s - 1) ^ 4 * (5 * s ^ 3 + 20 * s ^ 2 + 29 * s + 16) := by positivity
  linarith

lemma taylor_hi {x s : ℝ} (hx : 0 ≤ x) (hs : s = Real.sqrt (1 + x)) :
    1 ≤ s * (1 - x / 2 + 3 / 8 * x ^ 2) := by
  have h1 : 1 ≤ s := by rw [hs]; exact Real.le_sqrt_of_sq_le (by linarith)
  have h2 : s ^ 2 = 1 + x := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hx' : x = s ^ 2 - 1 := by linarith
  subst hx'
  have : s * (1 - (s ^ 2 - 1) / 2 + 3 / 8 * (s ^ 2 - 1) ^ 2) - 1
      = (s - 1) ^ 3 * (3 * s ^ 2 + 9 * s + 8) / 8 := by ring
  have h3 : 0 ≤ (s - 1) ^ 3 * (3 * s ^ 2 + 9 * s + 8) := by
    have : 0 ≤ s - 1 := by linarith
    positivity
  linarith

/-- `N / s ≥ N * L` when `N ≥ 0`, `s > 0` and `s * L ≤ 1`. -/
lemma div_ge_mul {N s L : ℝ} (hN : 0 ≤ N) (hs : 0 < s) (h : s * L ≤ 1) : N * L ≤ N / s := by
  rw [le_div_iff₀ hs]; nlinarith
/-- `N / s ≤ N * L` when `N ≥ 0`, `s > 0` and `1 ≤ s * L`. -/
lemma div_le_mul {N s L : ℝ} (hN : 0 ≤ N) (hs : 0 < s) (h : 1 ≤ s * L) : N / s ≤ N * L := by
  rw [div_le_iff₀ hs]; nlinarith
/-- `N / s ≥ N * L` when `N ≤ 0`, `s > 0` and `1 ≤ s * L`. -/
lemma div_ge_mul' {N s L : ℝ} (hN : N ≤ 0) (hs : 0 < s) (h : 1 ≤ s * L) : N * L ≤ N / s := by
  rw [le_div_iff₀ hs]; nlinarith

lemma near_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1 / 200) : F c < 0 := by
  have ha := Real.sqrt_pos.2 (show (0 : ℝ) < 1 + 12 * c by linarith)
  have hb := Real.sqrt_pos.2 (show (0 : ℝ) < 1 + 27 * c by linarith)
  have hd := Real.sqrt_pos.2 (show (0 : ℝ) < 1 + 108 * c by linarith)
  have e1 := div_ge_mul (show 0 ≤ 5 + 54 * c by linarith) ha
    (taylor_lo (x := 12 * c) (by linarith) rfl)
  have e2 := div_ge_mul (show (0 : ℝ) ≤ 2 by norm_num) hb
    (taylor_lo (x := 27 * c) (by linarith) rfl)
  have e3 := div_le_mul (show 0 ≤ 5 + 162 * c by linarith) hd
    (taylor_hi (x := 108 * c) (by linarith) rfl)
  have hq : 29160 * c ^ 3 + 5765391 * c ^ 2 / 8 + 50517 * c / 4 - 105 < 0 := by
    nlinarith [sq_nonneg c, mul_pos hc0 hc0]
  have hpoly : 2 - (5 + 54 * c) * (1 - 12 * c / 2 + 3 / 8 * (12 * c) ^ 2 - 5 / 16 * (12 * c) ^ 3)
      + (5 + 162 * c) * (1 - 108 * c / 2 + 3 / 8 * (108 * c) ^ 2)
      - 2 * (1 - 27 * c / 2 + 3 / 8 * (27 * c) ^ 2 - 5 / 16 * (27 * c) ^ 3)
      = c * (29160 * c ^ 3 + 5765391 * c ^ 2 / 8 + 50517 * c / 4 - 105) := by ring
  have : c * (29160 * c ^ 3 + 5765391 * c ^ 2 / 8 + 50517 * c / 4 - 105) < 0 :=
    mul_neg_of_pos_of_neg hc0 hq
  have h1 : (-5 - 162 * c) / Real.sqrt (1 + 108 * c) = -((5 + 162 * c) / Real.sqrt (1 + 108 * c)) := by
    rw [← neg_div]; ring_nf
  have h2 : (-2 + 0 * c) / Real.sqrt (1 + 27 * c) = -(2 / Real.sqrt (1 + 27 * c)) := by
    rw [← neg_div]; ring_nf
  unfold F
  rw [h1, h2]
  linarith

noncomputable def Fd (x : ℝ) : ℝ :=
  0 - 1 * ((24 + 324 * x) / Real.sqrt (1 + 12 * x) ^ 3)
    - (108 - 8748 * x) / Real.sqrt (1 + 108 * x) ^ 3
    + (54 + 0 * x) / (2 * Real.sqrt (1 + 27 * x) ^ 3)

lemma F_deriv (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (Fd x) x := by
  have h1 := term_deriv 5 54 0 12 x (by linarith)
  have h2 := term_deriv (-2) 0 0 27 x (by linarith)
  have h3 := term_deriv (-5) (-162) 0 108 x (by linarith)
  have hl : HasDerivAt (fun c : ℝ => 2 + 0 * c) 0 x := by
    simpa using ((hasDerivAt_id' x).const_mul (0 : ℝ)).const_add (2 : ℝ)
  have := ((hl.sub (h1.const_mul 1)).sub h3).add h2
  have hF : F = fun c => 2 + 0 * c - 1 * ((5 + 54 * c + 0 * c ^ 2) / Real.sqrt (1 + 12 * c))
      - (-5 + (-162) * c + 0 * c ^ 2) / Real.sqrt (1 + 108 * c)
      + (-2 + 0 * c + 0 * c ^ 2) / Real.sqrt (1 + 27 * c) := by
    funext c; unfold F; ring
  rw [hF]
  exact this.congr_deriv (by unfold Fd; ring)

lemma box_dpos (x0 x1 alo ahi blo bhi dlo dhi U1 U3 L2 : ℝ)
    (h0 : 0 ≤ x0)
    (ha0 : 0 < alo) (ha1 : alo ^ 2 ≤ 1 + 12 * x0) (ha2 : 1 + 12 * x1 ≤ ahi ^ 2) (ha3 : 0 ≤ ahi)
    (hb0 : 0 < blo) (hb1 : blo ^ 2 ≤ 1 + 27 * x0) (hb2 : 1 + 27 * x1 ≤ bhi ^ 2) (hb3 : 0 ≤ bhi)
    (hd0 : 0 < dlo) (hd1 : dlo ^ 2 ≤ 1 + 108 * x0) (hd2 : 1 + 108 * x1 ≤ dhi ^ 2) (hd3 : 0 ≤ dhi)
    (h1a : 24 + 324 * x1 ≤ U1 * alo ^ 3) (h1b : 24 + 324 * x1 ≤ U1 * ahi ^ 3)
    (h3a : 108 - 8748 * x0 ≤ U3 * dlo ^ 3)
    (h3b : 108 - 8748 * x0 ≤ U3 * dhi ^ 3)
    (h2a : L2 * blo ^ 3 ≤ 54 + 0 * x1)
    (h2b : L2 * bhi ^ 3 ≤ 54 + 0 * x1)
    (hsum : 0 < 0 - 1 * U1 - U3 + L2 / 2) :
    ∀ c ∈ Set.Icc x0 x1, 0 < Fd c := by
  rintro c ⟨hc0, hc1⟩
  have sa1 : alo ≤ Real.sqrt (1 + 12 * c) := sqrt_ge ha0.le ha1 (by linarith)
  have sa2 : Real.sqrt (1 + 12 * c) ≤ ahi := sqrt_le' ha3 ha2 (by linarith)
  have sb1 : blo ≤ Real.sqrt (1 + 27 * c) := sqrt_ge hb0.le hb1 (by linarith)
  have sb2 : Real.sqrt (1 + 27 * c) ≤ bhi := sqrt_le' hb3 hb2 (by linarith)
  have sd1 : dlo ≤ Real.sqrt (1 + 108 * c) := sqrt_ge hd0.le hd1 (by linarith)
  have sd2 : Real.sqrt (1 + 108 * c) ≤ dhi := sqrt_le' hd3 hd2 (by linarith)
  have e1 := ub_gen (pow_pos ha0 3) (pow_le_pow_left₀ ha0.le sa1 3) (pow_le_pow_left₀ (ha0.le.trans sa1) sa2 3)
    (show 24 + 324 * c ≤ 24 + 324 * x1 by nlinarith) h1a h1b
  have e3 := ub_gen (pow_pos hd0 3) (pow_le_pow_left₀ hd0.le sd1 3) (pow_le_pow_left₀ (hd0.le.trans sd1) sd2 3)
    (show 108 - 8748 * c ≤ 108 - 8748 * x0 by nlinarith) h3a h3b
  have e2 := lb_gen (pow_pos hb0 3) (pow_le_pow_left₀ hb0.le sb1 3) (pow_le_pow_left₀ (hb0.le.trans sb1) sb2 3)
    (show 54 + 0 * x1 ≤ 54 + 0 * c by nlinarith) h2a h2b
  have e4 : (54 + 0 * c) / (2 * Real.sqrt (1 + 27 * c) ^ 3)
      = (54 + 0 * c) / Real.sqrt (1 + 27 * c) ^ 3 / 2 := by ring
  unfold Fd
  linarith

structure Box where
  x0 : ℚ
  x1 : ℚ
  alo : ℚ
  ahi : ℚ
  blo : ℚ
  bhi : ℚ
  dlo : ℚ
  dhi : ℚ
  t1 : ℚ
  t3 : ℚ
  t2 : ℚ

def Box.sq (b : Box) : Bool :=
  decide (0 ≤ b.x0) && (decide (b.x0 ≤ b.x1) &&
  (decide (0 < b.alo) && (decide (b.alo ^ 2 ≤ 1 + 12 * b.x0) && (decide (1 + 12 * b.x1 ≤ b.ahi ^ 2) && (decide (0 ≤ b.ahi) &&
  (decide (0 < b.blo) && (decide (b.blo ^ 2 ≤ 1 + 27 * b.x0) && (decide (1 + 27 * b.x1 ≤ b.bhi ^ 2) && (decide (0 ≤ b.bhi) &&
  (decide (0 < b.dlo) && (decide (b.dlo ^ 2 ≤ 1 + 108 * b.x0) && (decide (1 + 108 * b.x1 ≤ b.dhi ^ 2) && decide (0 ≤ b.dhi)))))))))))))

def Box.okNeg (b : Box) : Bool :=
  b.sq && (
  decide (b.t1 * b.alo ≤ 5 + 54 * b.x0) && (decide (b.t1 * b.ahi ≤ 5 + 54 * b.x0) &&
  (decide (b.t3 * b.dlo ≤ -5 - 162 * b.x1) && (decide (b.t3 * b.dhi ≤ -5 - 162 * b.x1) &&
  (decide (-2 + 0 * b.x0 ≤ b.t2 * b.blo) && (decide (-2 + 0 * b.x0 ≤ b.t2 * b.bhi) &&
  decide (2 + 0 * b.x1 - 1 * b.t1 - b.t3 + b.t2 < 0)))))))

def Box.okPos (b : Box) : Bool :=
  b.sq && (
  decide (5 + 54 * b.x1 ≤ b.t1 * b.alo) && (decide (5 + 54 * b.x1 ≤ b.t1 * b.ahi) &&
  (decide (-5 - 162 * b.x0 ≤ b.t3 * b.dlo) && (decide (-5 - 162 * b.x0 ≤ b.t3 * b.dhi) &&
  (decide (b.t2 * b.blo ≤ -2 + 0 * b.x1) && (decide (b.t2 * b.bhi ≤ -2 + 0 * b.x1) &&
  decide (0 < 2 + 0 * b.x0 - 1 * b.t1 - b.t3 + b.t2)))))))

def Box.okD (b : Box) : Bool :=
  b.sq && (
  decide (24 + 324 * b.x1 ≤ b.t1 * b.alo ^ 3) && (decide (24 + 324 * b.x1 ≤ b.t1 * b.ahi ^ 3) &&
  (decide (108 - 8748 * b.x0 ≤ b.t3 * b.dlo ^ 3) && (decide (108 - 8748 * b.x0 ≤ b.t3 * b.dhi ^ 3) &&
  (decide (b.t2 * b.blo ^ 3 ≤ 54 + 0 * b.x1) && (decide (b.t2 * b.bhi ^ 3 ≤ 54 + 0 * b.x1) &&
  decide (0 < 0 - 1 * b.t1 - b.t3 + b.t2 / 2)))))))

lemma Box.sound_neg (b : Box) (h : b.okNeg = true) : ∀ c ∈ Set.Icc (b.x0 : ℝ) b.x1, F c < 0 := by
  simp only [Box.okNeg, Box.sq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13, h14, h15, h16, h17, h18, h19⟩ := h
  apply box_neg (b.x0 : ℝ) b.x1 b.alo b.ahi b.blo b.bhi b.dlo b.dhi b.t1 b.t3 b.t2 <;> exact_mod_cast (by assumption)

lemma Box.sound_pos (b : Box) (h : b.okPos = true) : ∀ c ∈ Set.Icc (b.x0 : ℝ) b.x1, 0 < F c := by
  simp only [Box.okPos, Box.sq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13, h14, h15, h16, h17, h18, h19⟩ := h
  apply box_pos (b.x0 : ℝ) b.x1 b.alo b.ahi b.blo b.bhi b.dlo b.dhi b.t1 b.t3 b.t2 <;> exact_mod_cast (by assumption)

lemma Box.sound_d (b : Box) (h : b.okD = true) : ∀ c ∈ Set.Icc (b.x0 : ℝ) b.x1, 0 < Fd c := by
  simp only [Box.okD, Box.sq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13, h14, h15, h16, h17, h18, h19⟩ := h
  apply box_dpos (b.x0 : ℝ) b.x1 b.alo b.ahi b.blo b.bhi b.dlo b.dhi b.t1 b.t3 b.t2 <;> exact_mod_cast (by assumption)

def chain (ok : Box → Bool) : ℚ → List Box → ℚ → Bool
  | _, [], _ => false
  | a, [b], e => decide (b.x0 = a) && (ok b && decide (b.x1 = e))
  | a, b :: b' :: bs, e => decide (b.x0 = a) && (ok b && chain ok b.x1 (b' :: bs) e)

lemma chain_sound (P : ℝ → Prop) (ok : Box → Bool)
    (hok : ∀ b : Box, ok b = true → ∀ c ∈ Set.Icc (b.x0 : ℝ) b.x1, P c) :
    ∀ (l : List Box) (a e : ℚ), chain ok a l e = true → ∀ c ∈ Set.Icc (a : ℝ) e, P c
  | [], a, e, h => by simp [chain] at h
  | [b], a, e, h => by
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h3
    exact hok b h2
  | b :: b' :: bs, a, e, h => by
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1
    exact cover_join (hok b h2) (chain_sound P ok hok (b' :: bs) b.x1 e h3)

def negBoxes : List Box := [
  ⟨(1/200), (3/500), (102956301/100000000), (103537433/100000000), (53268189/50000000), (13474513/12500000), (3878023/3125000), (128374453/100000000), (101798931/20000000), (-120309369/25000000), (-92767731/50000000)⟩,
  ⟨(3/500), (3/400), (12942179/12500000), (52201533/50000000), (107796103/100000000), (109658561/100000000), (32093613/25000000), (134536241/100000000), (509946709/100000000), (-484130597/100000000), (-182384301/100000000)⟩,
  ⟨(3/400), (39/4000), (20880613/20000000), (105688221/100000000), (342683/312500), (22478879/20000000), (1681703/1250000), (143282937/100000000), (127852469/25000000), (-244525193/50000000), (-11121551/6250000)⟩,
  ⟨(39/4000), (11437/1000000), (5284411/5000000), (106641643/100000000), (56197197/50000000), (57201377/50000000), (17910367/12500000), (149505719/100000000), (10364619/2000000), (-59783759/12500000), (-87410483/50000000)⟩,
  ⟨(11437/1000000), (13967/1000000), (53320821/50000000), (108055727/100000000), (114402753/100000000), (7334393/6250000), (74752859/50000000), (158380429/100000000), (519879709/100000000), (-19431107/4000000), (-85214959/50000000)⟩,
  ⟨(13967/1000000), (1983/125000), (54027863/50000000), (27275997/25000000), (117350287/100000000), (59756339/50000000), (39595107/25000000), (164721341/100000000), (16481461/3125000), (-238980539/50000000), (-83673131/50000000)⟩,
  ⟨(1983/125000), (18709/1000000), (109103987/100000000), (11065749/10000000), (119512677/100000000), (12268427/10000000), (8236067/5000000), (173797929/100000000), (52925979/10000000), (-121885513/25000000), (-163020083/100000000)⟩,
  ⟨(18709/1000000), (10421/500000), (110657489/100000000), (2236161/2000000), (122684269/100000000), (1562617/1250000), (21724741/12500000), (90151761/50000000), (537553959/100000000), (-60245281/12500000), (-7999401/5000000)⟩,
  ⟨(10421/500000), (24041/1000000), (111808049/100000000), (56755881/50000000), (125009359/100000000), (64208781/50000000), (180303521/100000000), (94821253/50000000), (67454111/12500000), (-493314937/100000000), (-77870969/50000000)⟩,
  ⟨(24041/1000000), (661/25000), (113511761/100000000), (5738641/5000000), (128417561/100000000), (3272881/2500000), (37928501/20000000), (196354781/100000000), (109750967/20000000), (-122378683/25000000), (-152770601/100000000)⟩,
  ⟨(661/25000), (28239/1000000), (114772819/100000000), (14463683/12500000), (130915239/100000000), (132757411/100000000), (9817739/5000000), (25155181/12500000), (555508579/100000000), (-487623373/100000000), (-150650723/100000000)⟩,
  ⟨(28239/1000000), (30937/1000000), (115709463/100000000), (117100129/100000000), (13275741/10000000), (16934151/12500000), (201241447/100000000), (20835537/10000000), (557207413/100000000), (-497501591/100000000), (-73815333/50000000)⟩,
  ⟨(30937/1000000), (103/3125), (3659379/3125000), (11813213/10000000), (135473207/100000000), (68737181/50000000), (208355369/100000000), (213534073/100000000), (4517381/800000), (-62030559/12500000), (-145481671/100000000)⟩,
  ⟨(103/3125), (17997/500000), (118132129/100000000), (23932639/20000000), (137474361/100000000), (2808443/2000000), (26691759/12500000), (221073563/100000000), (283288441/50000000), (-126806789/25000000), (-17803459/12500000)⟩,
  ⟨(17997/500000), (38269/1000000), (59831597/50000000), (12079851/10000000), (140422149/100000000), (35648133/25000000), (110536781/50000000), (113281199/50000000), (114962941/20000000), (-506599609/100000000), (-140259799/100000000)⟩,
  ⟨(38269/1000000), (1/25), (120798509/100000000), (121655251/100000000), (142592531/100000000), (36055513/25000000), (226562397/100000000), (57662813/25000000), (580864857/100000000), (-506703679/100000000), (-17334381/12500000)⟩]

def posBoxes : List Box := [
  ⟨(9/80), (227/2000), (153297097/100000000), (38421999/25000000), (12558457/6250000), (50401513/25000000), (362629287/100000000), (364115367/100000000), (362987957/50000000), (-637847289/100000000), (-99534521/100000000)⟩,
  ⟨(227/2000), (23/200), (30737599/20000000), (154272487/100000000), (201606051/100000000), (50651999/25000000), (182057683/50000000), (183166591/50000000), (729399847/100000000), (-638407907/100000000), (-24800843/25000000)⟩,
  ⟨(23/200), (469/4000), (77136243/50000000), (77572547/50000000), (40521599/20000000), (204101691/100000000), (366333181/100000000), (92408739/25000000), (734512051/100000000), (-127855873/20000000), (-24678197/25000000)⟩,
  ⟨(469/4000), (193/1600), (155145093/100000000), (156444879/100000000), (20410169/10000000), (103160979/50000000), (73926991/20000000), (374533043/100000000), (742127887/100000000), (-160162771/25000000), (-9799037/10000000)⟩,
  ⟨(193/1600), (30789/250000), (78222439/50000000), (157412579/100000000), (206321957/100000000), (207971441/100000000), (187266521/50000000), (378164621/100000000), (372349167/50000000), (-648956793/100000000), (-48467939/50000000)⟩,
  ⟨(30789/250000), (15869/125000), (78706289/50000000), (19856611/12500000), (2599643/1250000), (105210551/50000000), (18908231/5000000), (5992919/1562500), (753142357/100000000), (-325270227/50000000), (-96167051/100000000)⟩,
  ⟨(15869/125000), (129799/1000000), (158852887/100000000), (1249411/781250), (210421101/100000000), (106119897/50000000), (76709363/20000000), (96883603/25000000), (30239667/4000000), (-82464367/12500000), (-47523751/50000000)⟩,
  ⟨(129799/1000000), (134069/1000000), (159924607/100000000), (40379667/25000000), (212239793/100000000), (107469333/50000000), (387534411/100000000), (98359837/25000000), (76534351/10000000), (-330768111/50000000), (-23558259/25000000)⟩,
  ⟨(134069/1000000), (5/36), (161518667/100000000), (163299317/100000000), (42987733/20000000), (54486237/25000000), (393439347/100000000), (400000001/100000000), (773904357/100000000), (-83497431/12500000), (-93049801/100000000)⟩]

def dBoxes : List Box := [
  ⟨(1/25), (41/1000), (486621/400000), (30536863/25000000), (144222051/100000000), (14515509/10000000), (230651251/100000000), (116490343/50000000), (2070760789/100000000), (-956493491/50000000), (1765618829/100000000)⟩,
  ⟨(41/1000), (17/400), (122147451/100000000), (61441029/50000000), (145155089/100000000), (146543509/100000000), (46596137/20000000), (236431809/100000000), (2072496279/100000000), (-474155933/25000000), (428977001/25000000)⟩,
  ⟨(17/400), (179/4000), (122882057/100000000), (24795161/20000000), (36635877/25000000), (148601817/100000000), (3694247/1562500), (120758023/50000000), (82993489/4000000), (-468123417/25000000), (822794547/50000000)⟩,
  ⟨(179/4000), (77/1600), (30993951/25000000), (125598567/100000000), (18575227/12500000), (75818451/50000000), (48303209/20000000), (124473893/50000000), (415558453/20000000), (-459332213/25000000), (1548741909/100000000)⟩,
  ⟨(77/1600), (53187/1000000), (62799283/50000000), (127993907/100000000), (151636901/100000000), (78039237/50000000), (49789557/20000000), (2596959/1000000), (65033417/3125000), (-893543281/50000000), (710124887/50000000)⟩,
  ⟨(53187/1000000), (3039/50000), (63996953/50000000), (131505133/100000000), (156078473/100000000), (32502677/20000000), (259695899/100000000), (55006327/20000000), (416745769/20000000), (-1717357073/100000000), (314533103/25000000)⟩,
  ⟨(3039/50000), (72169/1000000), (32876283/25000000), (34150659/25000000), (20314173/12500000), (171713803/100000000), (137515817/50000000), (148275521/50000000), (520873451/25000000), (-81233213/5000000), (533271217/50000000)⟩,
  ⟨(72169/1000000), (8071/100000), (27320527/20000000), (35075989/25000000), (85856901/50000000), (2785973/1562500), (296551041/100000000), (311715897/100000000), (1967406281/100000000), (-345567137/20000000), (95262753/10000000)⟩,
  ⟨(8071/100000), (93521/1000000), (28060791/20000000), (18209939/12500000), (178302271/100000000), (93875809/50000000), (38964487/12500000), (333170647/100000000), (1966058879/100000000), (-1617104487/100000000), (101988853/12500000)⟩,
  ⟨(93521/1000000), (103129/1000000), (145679511/100000000), (74792179/50000000), (187751617/100000000), (97268739/50000000), (166585323/50000000), (348395351/100000000), (928519099/50000000), (-1679251463/100000000), (146694527/20000000)⟩,
  ⟨(103129/1000000), (9/80), (149584357/100000000), (76648549/50000000), (194537477/100000000), (200935313/100000000), (6967907/2000000), (45328661/12500000), (361216653/20000000), (-104089333/6250000), (166404461/25000000)⟩]

lemma negAll : ∀ c ∈ Set.Icc (1 / 200 : ℝ) (1 / 25), F c < 0 := by
  have := chain_sound (fun c => F c < 0) Box.okNeg Box.sound_neg negBoxes (1 / 200) (1 / 25)
    (by decide +kernel)
  simpa using this

lemma posAll : ∀ c ∈ Set.Icc (9 / 80 : ℝ) (5 / 36), 0 < F c := by
  have := chain_sound (fun c => 0 < F c) Box.okPos Box.sound_pos posBoxes (9 / 80) (5 / 36)
    (by decide +kernel)
  simpa using this

lemma dAll : ∀ c ∈ Set.Icc (1 / 25 : ℝ) (9 / 80), 0 < Fd c := by
  have := chain_sound (fun c => 0 < Fd c) Box.okD Box.sound_d dBoxes (1 / 25) (9 / 80)
    (by decide +kernel)
  simpa using this

lemma F_mono : StrictMonoOn F (Set.Icc (1 / 25 : ℝ) (9 / 80)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro x hx
    exact (F_deriv x (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(F_deriv x (by linarith [hx.1])).deriv]
    exact dAll x ⟨hx.1.le, hx.2.le⟩

lemma F_cont : ContinuousOn F (Set.Icc (1 / 25 : ℝ) (9 / 80)) := fun x hx =>
  (F_deriv x (by linarith [hx.1])).continuousAt.continuousWithinAt

lemma cutoff : ∃ cl : ℝ, 0 < cl ∧ cl < 5 / 36 ∧ ∀ c : ℝ, 0 < c → c < 5 / 36 →
    (cl < c → 0 < F c) ∧ (c < cl → F c < 0) := by
  have hA : F (1 / 25) < 0 := negAll _ ⟨by norm_num, le_refl _⟩
  have hB : 0 < F (9 / 80) := posAll _ ⟨le_refl _, by norm_num⟩
  obtain ⟨cl, ⟨hcl1, hcl2⟩, hFcl⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 25 : ℝ) ≤ 9 / 80) F_cont ⟨hA.le, hB.le⟩
  refine ⟨cl, by linarith, by linarith, fun c hc0 hc1 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases le_total (9 / 80) c with h' | h'
    · exact posAll c ⟨h', hc1.le⟩
    · have := F_mono ⟨hcl1, hcl2⟩ ⟨by linarith, h'⟩ h
      linarith
  · rcases le_total c (1 / 200) with h' | h'
    · exact near_zero c hc0 h'
    rcases le_total c (1 / 25) with h'' | h''
    · exact negAll c ⟨h', h''⟩
    · have := F_mono ⟨h'', by linarith⟩ ⟨hcl1, hcl2⟩ h
      linarith

end BBDP2Aux

open BBDisclosure.Total

theorem solution :
    ∃ ch : ℝ, 0 < ch ∧ ch < 5 / 36 ∧
      ∀ c : ℝ, 0 < c → c < 5 / 36 →
        ∀ (sU : SPE_U) (sB : SPE_BBD), IsSymSPE_U c sU → IsSymSPE_BBD c sB →
          (ch < c → sU.pStar < sB.pStar ∧ firstProfitA_U sU < firstProfitA_BBD sB ∧
              firstProfitB_U sU < firstProfitB_BBD sB) ∧
          (c < ch → sB.pStar < sU.pStar ∧ firstProfitA_BBD sB < firstProfitA_U sU ∧
              firstProfitB_BBD sB < firstProfitB_U sU) := by
  obtain ⟨ch, h0, h1, hch⟩ := BBDP2Aux.cutoff
  refine ⟨ch, h0, h1, fun c hc0 hc1 sU sB hU hB => ?_⟩
  obtain ⟨hpU, hxU⟩ := (equation_9 c hc0 hc1).2 sU hU
  obtain ⟨hpB, hxB⟩ := (equation_17 c hc0 hc1).2 sB hB
  have key : 3 * ((4 / 3 - c * (5 + 54 * c) / (3 * Real.sqrt (1 + 12 * c))
            + c * (5 + 162 * c) / (3 * Real.sqrt (1 + 108 * c)))
        - 2 / 3 * (2 - c + c / Real.sqrt (1 + 27 * c))) = c * BBDP2Aux.F c := by
    unfold BBDP2Aux.F; ring
  unfold firstProfitA_U firstProfitA_BBD firstProfitB_U firstProfitB_BBD
  rw [hxU, hxB]
  rw [← hpU, ← hpB] at key
  obtain ⟨k1, k2⟩ := hch c hc0 hc1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := mul_pos hc0 (k1 h)
    refine ⟨by linarith, by nlinarith, by nlinarith⟩
  · have := mul_neg_of_pos_of_neg hc0 (k2 h)
    refine ⟨by linarith, by nlinarith, by nlinarith⟩
