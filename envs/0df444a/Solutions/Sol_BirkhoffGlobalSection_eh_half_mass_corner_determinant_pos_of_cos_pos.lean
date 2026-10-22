-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_half_mass_corner_determinant_pos_of_cos_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:00:07.268991+00:00
-- url     : https://prove2.me/submissions/81b88a1c-b6c5-46c7-ba8a-727700f9b0af

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_00
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_01
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_02
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_03
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_04
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_05
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_06
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_07
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_08
import Theorems.Thm_BirkhoffGlobalSection_EHConvex_corner_cert_part_09

/-!
# Corner determinants of the equal-mass convexity criterion (algebraic layer)

Liu--Salomão §9.3 in the variables `a = cosh x₁`, `b = cos x₂`, `P = |sinh x₁|`, `Q = |sin x₂|`.
See `CORNER_PLAN.md`.
-/

namespace BirkhoffGlobalSection.EHConvex.Corner

noncomputable section

/-- The equal-mass potential in the variables `a = cosh x₁`, `b = cos x₂`. -/
def Vp (c a b : ℝ) : ℝ := c * (a ^ 2 - b ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 - b ^ 2 * (1 - b ^ 2) / 32

/-- `V₁ = P · w1`. -/
def w1 (c a : ℝ) : ℝ := c * a / 2 - 1 / 2 - a * (2 * a ^ 2 - 1) / 16

/-- `V₂ = Q · w2`. -/
def w2 (c b : ℝ) : ℝ := b * (c / 2 - (2 * b ^ 2 - 1) / 16)

def v11 (c a : ℝ) : ℝ := c * (2 * a ^ 2 - 1) / 2 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16

def v22 (c b : ℝ) : ℝ := c * (2 * b ^ 2 - 1) / 2 - (2 * (2 * b ^ 2 - 1) ^ 2 - 1) / 16

/-- `r = √(-2V)`. -/
def rr (c a b : ℝ) : ℝ := Real.sqrt (-2 * Vp c a b)

/-- The lower `c`-corner `V₁₁ - r |sinh 2x₁| / 2`. -/
def cm (c a b P : ℝ) : ℝ := v11 c a - a * P * rr c a b

/-- Liu--Salomão's `D̂`: the lower `d`-corner with `r` replaced by its value at `x₁ = 0`. -/
def Dh (c b Q : ℝ) : ℝ := v22 c b - b * Q * rr c 1 b

def W0 (c a b P : ℝ) : ℝ := P ^ 2 * w1 c a ^ 2 / cm c a b P + rr c a b ^ 2

def I0 (c a b P Q : ℝ) : ℝ := Q ^ 2 * w2 c b ^ 2 + Dh c b Q * W0 c a b P

/-! ## L0, L1: the Hill box -/

theorem a_le_two_of_hill {c a b : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (h0 : a ^ 2 ≤ 2 * c) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hV : Vp c a b ≤ 0) : a ≤ 2 := by
  by_contra h
  push Not at h
  unfold Vp at hV
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hbt : c * b ^ 2 / 4 + b ^ 2 * (1 - b ^ 2) / 32 ≤ c / 4 := by
    nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ 1 - b ^ 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - b ^ 2) (by linarith : (0:ℝ) ≤ c - 1 / 8)]
  have hq : a ^ 2 * (a ^ 2 - 1) ≤ 2 * c * (a ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right h0 (by nlinarith)
  nlinarith [mul_pos (by linarith : (0:ℝ) < a - 2) (by linarith : (0:ℝ) < a),
    mul_pos (mul_pos (by linarith : (0:ℝ) < a - 2) (by linarith : (0:ℝ) < a))
      (by linarith : (0:ℝ) < a)]

theorem Vp_b_zero_pos {c a : ℝ} (hc : 2 < c) (ha : 1 ≤ a) (ha2 : a ≤ 2) : 0 < Vp c a 0 := by
  unfold Vp
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : 0 ≤ 2 - a := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h1, mul_pos (by linarith : (0:ℝ) < c - 2)
    (by nlinarith : (0:ℝ) < a ^ 2)]

theorem b_pos {c a b : ℝ} (hc : 2 < c) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b)
    (hV : Vp c a b ≤ 0) : 0 < b := by
  rcases hb0.lt_or_eq with h | h
  · exact h
  · subst h; linarith [Vp_b_zero_pos hc ha ha2]

/-- `V` increases with `a = cosh x₁` on the box. -/
theorem Vp_one_le {c a b : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (ha2 : a ≤ 2) : Vp c 1 b ≤ Vp c a b := by
  unfold Vp
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : 0 ≤ 2 - a := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h1, mul_nonneg (mul_nonneg h1 h2) h2,
    mul_nonneg h1 (by linarith : (0:ℝ) ≤ c - 2), mul_nonneg (mul_nonneg h1 h1) (by linarith : (0:ℝ) ≤ c - 2)]

/-- `V` increases with the energy parameter `c`. -/
theorem Vp_mono_c {c c' a b : ℝ} (hcc : c' ≤ c) (hab : b ^ 2 ≤ a ^ 2) : Vp c' a b ≤ Vp c a b := by
  unfold Vp; nlinarith [mul_nonneg (sub_nonneg.2 hcc) (sub_nonneg.2 hab)]

/-- `V` decreases with `b = cos x₂`. -/
theorem Vp_anti_b {c a b b' : ℝ} (hc : 2 ≤ c) (hb : 0 ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ 1) :
    Vp c a b' ≤ Vp c a b := by
  unfold Vp
  have h1 : 0 ≤ b' - b := by linarith
  have h2 : 0 ≤ b + b' := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) (by linarith : (0:ℝ) ≤ c - 2),
    mul_nonneg (mul_nonneg h1 h2) (by nlinarith : (0:ℝ) ≤ 2 - b ^ 2 - b' ^ 2 + 1)]

/-! ## L2: the lower `c`-corner is positive for `c ≥ 2` -/

theorem poly_H1_strict {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hW : 0 ≤ 1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32)) :
    0 < 2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16 ∧
    (1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32)) * (a ^ 2 * (a ^ 2 - 1)) <
      (2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16) ^ 2 := by
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : 0 ≤ 2 - a := by linarith
  have h3 : a ≤ 181 / 100 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h1]
  have h4 : 0 ≤ 181 / 100 - a := by linarith
  constructor
  · nlinarith [mul_nonneg h1 h4, mul_nonneg (mul_nonneg h1 h4) h1, mul_nonneg (mul_nonneg h1 h4) h4]
  · nlinarith [mul_nonneg h1 h4, mul_nonneg (mul_nonneg h1 h4) h1, mul_nonneg (mul_nonneg h1 h4) h4,
      mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 h4), mul_nonneg (mul_nonneg h4 h4) (mul_nonneg h1 h4)]

theorem cm_pos {c a b P : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hV : Vp c a b ≤ 0) : 0 < cm c a b P := by
  set ρ2 := 1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32) with hρ2
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hR : -2 * Vp c a b ≤ ρ2 := by
    have := Vp_mono_c (c := c) (c' := 2) (a := a) (b := b) hc (by nlinarith)
    unfold Vp at this ⊢
    nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ 1 - b ^ 2)]
  have hρ0 : 0 ≤ ρ2 := by linarith
  obtain ⟨hq0, hqsq⟩ := poly_H1_strict ha ha2 hρ0
  have hsq : rr c a b ≤ Real.sqrt ρ2 := Real.sqrt_le_sqrt hR
  have hkey : Real.sqrt ρ2 * (a * P) < 2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16 := by
    apply abs_lt_of_sq_lt_sq' _ hq0.le |>.2
    rw [mul_pow, mul_pow, Real.sq_sqrt hρ0, hP2]
    exact hqsq
  have hv11 : v11 c a = (2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16) +
      (c - 2) * (2 * a ^ 2 - 1) / 2 := by unfold v11; ring
  have hpos : 0 ≤ (c - 2) * (2 * a ^ 2 - 1) / 2 := by
    have : 0 ≤ 2 * a ^ 2 - 1 := by nlinarith
    have : 0 ≤ c - 2 := by linarith
    positivity
  have hprod : a * P * rr c a b ≤ Real.sqrt ρ2 * (a * P) := by
    rw [mul_comm (Real.sqrt ρ2)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  unfold cm
  rw [hv11]
  linarith

/-! ## L3: from the four corners to `I0` -/

theorem rr_sq {c a b : ℝ} (hV : Vp c a b ≤ 0) : rr c a b ^ 2 = -2 * Vp c a b :=
  Real.sq_sqrt (by linarith)

theorem w1_pos {c a : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (ha2 : a ≤ 2) : 0 < w1 c a := by
  unfold w1
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - 1) (by linarith : (0:ℝ) ≤ 2 - a),
    mul_nonneg (by linarith : (0:ℝ) ≤ c - 2) (by linarith : (0:ℝ) ≤ a)]

theorem w2_pos {c b : ℝ} (hc : 2 ≤ c) (hb : 0 < b) (hb1 : b ≤ 1) : 0 < w2 c b := by
  unfold w2
  have : 0 < c / 2 - (2 * b ^ 2 - 1) / 16 := by nlinarith
  positivity

theorem corner_of_I0 {c a b P Q σ τ : ℝ} (hc : 2 ≤ c) (hb' : 0 < b) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = 1 - b ^ 2)
    (hV : Vp c a b ≤ 0) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hI : Dh c b Q < 0 → 0 < I0 c a b P Q) :
    0 < rr c a b ^ 2 * (v11 c a + σ * a * P * rr c a b) * (v22 c b + τ * b * Q * rr c a b) +
      (v11 c a + σ * a * P * rr c a b) * (Q * w2 c b) ^ 2 +
      (v22 c b + τ * b * Q * rr c a b) * (P * w1 c a) ^ 2 := by
  have hb := hb'
  set r := rr c a b with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = -2 * Vp c a b := rr_sq hV
  have hrr0 : r ≤ rr c 1 b := Real.sqrt_le_sqrt (by linarith [Vp_one_le (b := b) hc ha ha2])
  have hcm := cm_pos hc ha ha2 hb0 hb1 hP hP2 hV
  set cc := v11 c a + σ * a * P * r with hcc
  set dd := v22 c b + τ * b * Q * r with hdd
  have haPr : 0 ≤ a * P * r := by positivity
  have hbQr : 0 ≤ b * Q * r := by positivity
  have hccm : cm c a b P ≤ cc := by
    unfold cm; rw [hcc, ← hr]; rcases hσ with h | h <;> subst h <;> linarith
  have hcc0 : 0 < cc := lt_of_lt_of_le hcm hccm
  have hddD : Dh c b Q ≤ dd := by
    unfold Dh; rw [hdd]
    have : b * Q * r ≤ b * Q * rr c 1 b := mul_le_mul_of_nonneg_left hrr0 (by positivity)
    rcases hτ with h | h <;> subst h <;> linarith
  rcases le_or_gt 0 dd with hd | hd
  · rcases hb1.lt_or_eq with hb1' | hb1'
    · have hQp : 0 < Q := by
        rcases hQ.lt_or_eq with h | h
        · exact h
        · rw [← h] at hQ2; nlinarith
      have h1 : 0 < cc * (Q * w2 c b) ^ 2 := by
        have := w2_pos hc hb hb1; positivity
      have h2 : 0 ≤ r ^ 2 * cc * dd := by positivity
      have h3 : 0 ≤ dd * (P * w1 c a) ^ 2 := by positivity
      linarith
    · -- `b = 1`: then `Q = 0` and `dd = c/2 - 1/16 > 0`
      subst hb1'
      have hQ0 : Q = 0 := by nlinarith
      have hdd' : dd = c / 2 - 1 / 16 := by rw [hdd, hQ0]; unfold v22; ring
      have hdpos : 0 < dd := by rw [hdd']; linarith
      rcases hP.lt_or_eq with hP' | hP'
      · have h1 : 0 < dd * (P * w1 c a) ^ 2 := by
          have := w1_pos hc ha ha2; positivity
        have h2 : 0 ≤ r ^ 2 * cc * dd := by positivity
        have h3 : 0 ≤ cc * (Q * w2 c 1) ^ 2 := by positivity
        linarith
      · have ha1 : a = 1 := by nlinarith
        subst ha1
        have hr1 : r ^ 2 = 1 := by rw [hr2]; unfold Vp; norm_num
        have h1 : 0 < r ^ 2 * cc * dd := by rw [hr1]; positivity
        have h3 : 0 ≤ cc * (Q * w2 c 1) ^ 2 := by positivity
        have h2 : 0 ≤ dd * (P * w1 c 1) ^ 2 := by positivity
        linarith
  · have hD0 : Dh c b Q < 0 := lt_of_le_of_lt hddD hd
    have hI0 := hI hD0
    set X := (P * w1 c a) ^ 2 with hX
    have hX0 : 0 ≤ X := by positivity
    -- `cc · X / cm ≥ X`
    have hdiv : X ≤ cc * X / cm c a b P := by
      rw [le_div_iff₀ hcm]; nlinarith
    have hI0' : I0 c a b P Q = Q ^ 2 * w2 c b ^ 2 + Dh c b Q * (X / cm c a b P + r ^ 2) := by
      unfold I0 W0; rw [hX, ← hr]; ring
    have key : cc * I0 c a b P Q ≤ r ^ 2 * cc * dd + cc * (Q * w2 c b) ^ 2 + dd * X := by
      rw [hI0']
      have e1 : cc * (Q ^ 2 * w2 c b ^ 2 + Dh c b Q * (X / cm c a b P + r ^ 2)) =
          cc * (Q * w2 c b) ^ 2 + Dh c b Q * (cc * X / cm c a b P) + Dh c b Q * cc * r ^ 2 := by
        ring
      rw [e1]
      have e2 : Dh c b Q * (cc * X / cm c a b P) ≤ Dh c b Q * X :=
        mul_le_mul_of_nonpos_left hdiv hD0.le
      have e3 : Dh c b Q * X ≤ dd * X := mul_le_mul_of_nonneg_right hddD hX0
      have e4 : Dh c b Q * cc * r ^ 2 ≤ dd * cc * r ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hddD hcc0.le) (sq_nonneg r)
      nlinarith
    have := mul_pos hcc0 hI0
    linarith

/-! ## L4: reduction to `c = 2` (no derivatives) -/

/-- The quadratic-form step: with `W' = W + aδ/2` and `C'' ≥ C + (a²-½)δ`,
`W'²/C'' ≤ W²/C + δ/2` (the form `C²/2 - aWC + (a²-½)W²` is `½(C-aW)² + (a²-1)W²/2 ≥ 0`). -/
theorem ratio_step {a W C C' δ : ℝ} (ha : 1 ≤ a) (hC : 0 < C) (hδ : 0 ≤ δ)
    (hC' : C + (a ^ 2 - 1 / 2) * δ ≤ C') :
    (W + a * δ / 2) ^ 2 / C' ≤ W ^ 2 / C + δ / 2 := by
  have hk : 0 ≤ a ^ 2 - 1 / 2 := by nlinarith
  have hC'' : 0 < C + (a ^ 2 - 1 / 2) * δ := by positivity
  have hC'0 : 0 < C' := by linarith
  calc (W + a * δ / 2) ^ 2 / C' ≤ (W + a * δ / 2) ^ 2 / (C + (a ^ 2 - 1 / 2) * δ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hC'' hC'
    _ ≤ W ^ 2 / C + δ / 2 := by
        rw [div_add' _ _ _ hC.ne', div_le_div_iff₀ hC'' hC]
        nlinarith [mul_nonneg hδ (sq_nonneg (C - a * W)),
          mul_nonneg hδ (mul_nonneg (by nlinarith : (0:ℝ) ≤ a ^ 2 - 1) (sq_nonneg W)),
          mul_nonneg (mul_nonneg hδ hδ) (mul_nonneg hC.le (by nlinarith : (0:ℝ) ≤ a ^ 2 - 1))]

theorem rr_le_two {c a b : ℝ} (hc : 2 ≤ c) (hab : b ^ 2 ≤ a ^ 2) : rr c a b ≤ rr 2 a b :=
  Real.sqrt_le_sqrt (by linarith [Vp_mono_c (a := a) (b := b) hc hab])

theorem W0_step {c a b P Q : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hQ2 : Q ^ 2 = 1 - b ^ 2)
    (hV : Vp c a b ≤ 0) :
    W0 c a b P ≤ W0 2 a b P - (c - 2) * Q ^ 2 / 2 := by
  have hab : b ^ 2 ≤ a ^ 2 := by nlinarith
  have hV2 : Vp 2 a b ≤ 0 := le_trans (Vp_mono_c hc hab) hV
  have hcm2 := cm_pos le_rfl ha ha2 hb0 hb1 hP hP2 hV2
  have hcm' : cm 2 a b P + (a ^ 2 - 1 / 2) * (c - 2) ≤ cm c a b P := by
    unfold cm
    have h1 : v11 c a = v11 2 a + (a ^ 2 - 1 / 2) * (c - 2) := by unfold v11; ring
    have h2 : a * P * rr c a b ≤ a * P * rr 2 a b :=
      mul_le_mul_of_nonneg_left (rr_le_two hc hab) (by positivity)
    linarith
  have hw : w1 c a = w1 2 a + a * (c - 2) / 2 := by unfold w1; ring
  have hstep := ratio_step (W := w1 2 a) ha hcm2 (by linarith : (0:ℝ) ≤ c - 2) hcm'
  rw [← hw] at hstep
  have hr2 : rr c a b ^ 2 = rr 2 a b ^ 2 - (c - 2) * (a ^ 2 - b ^ 2) / 2 := by
    rw [rr_sq hV, rr_sq hV2]; unfold Vp; ring
  unfold W0
  rw [hr2]
  have h1 := mul_le_mul_of_nonneg_left hstep (sq_nonneg P)
  have e1 : P ^ 2 * w1 c a ^ 2 / cm c a b P = P ^ 2 * (w1 c a ^ 2 / cm c a b P) := by ring
  have e2 : P ^ 2 * w1 2 a ^ 2 / cm 2 a b P = P ^ 2 * (w1 2 a ^ 2 / cm 2 a b P) := by ring
  have e3 : P ^ 2 * (w1 2 a ^ 2 / cm 2 a b P + (c - 2) / 2) =
      P ^ 2 * (w1 2 a ^ 2 / cm 2 a b P) + (c - 2) * (a ^ 2 - 1) / 2 := by rw [mul_add, hP2]; ring
  rw [e1, e2]
  rw [e3] at h1
  have e4 : (c - 2) * (a ^ 2 - b ^ 2) / 2 = (c - 2) * (a ^ 2 - 1) / 2 + (c - 2) * Q ^ 2 / 2 := by
    rw [hQ2]; ring
  linarith

theorem rr1_sq (c b : ℝ) : -2 * Vp c 1 b = 1 - c / 2 + (1 + 8 * c) * b ^ 2 / 16 - b ^ 4 / 16 := by
  unfold Vp; ring

/-- P3: if `D̂` decreases from `2` to `c`, then `b² < 25/64`. -/
theorem b_small_of_Dh_lt {c b Q : ℝ} (hc : 2 ≤ c) (hb : 0 < b) (hb1 : b ≤ 1) (hQ : 0 ≤ Q)
    (hQ2 : Q ^ 2 = 1 - b ^ 2) (hV1 : Vp c 1 b ≤ 0) (hlt : Dh c b Q < Dh 2 b Q) :
    b ^ 2 < 25 / 64 := by
  have hV12 : Vp 2 1 b ≤ 0 := le_trans (Vp_mono_c hc (by nlinarith)) hV1
  set r0 := rr c 1 b with hr0
  set r2 := rr 2 1 b with hr2
  have h0 : 0 ≤ r0 := Real.sqrt_nonneg _
  have h2 : 0 ≤ r2 := Real.sqrt_nonneg _
  have hle : r0 ≤ r2 := rr_le_two hc (by nlinarith)
  have hsq0 : r0 ^ 2 = 1 - c / 2 + (1 + 8 * c) * b ^ 2 / 16 - b ^ 4 / 16 := by
    rw [hr0, rr_sq hV1, rr1_sq]
  have hsq2 : r2 ^ 2 = b ^ 2 * (17 - b ^ 2) / 16 := by
    rw [hr2, rr_sq hV12, rr1_sq]; ring
  have hdiff : (r2 - r0) * (r2 + r0) = (c - 2) * Q ^ 2 / 2 := by
    rw [hQ2]; nlinarith [hsq0, hsq2]
  have hD : Dh c b Q - Dh 2 b Q = (c - 2) * (b ^ 2 - 1 / 2) + b * Q * (r2 - r0) := by
    unfold Dh; rw [← hr0, ← hr2]; unfold v22; ring
  have hbQ : 0 ≤ b * Q * (r2 - r0) := by have := sub_nonneg.2 hle; positivity
  -- so `c > 2` and `b² < 1/2`
  have hneg : (c - 2) * (1 / 2 - b ^ 2) > b * Q * (r2 - r0) := by linarith
  have hc2 : 0 < c - 2 := by
    rcases (sub_nonneg.2 hc).lt_or_eq with h | h
    · exact h
    · rw [← h] at hneg; linarith
  have hb2 : 0 < 1 / 2 - b ^ 2 := by
    by_contra h; push Not at h; nlinarith [mul_nonneg hc2.le (by linarith : (0:ℝ) ≤ b ^ 2 - 1 / 2)]
  -- multiply by `r2 + r0 ≤ 2 r2`
  have hmul : (c - 2) * (1 / 2 - b ^ 2) * (2 * r2) ≥ b * Q * ((c - 2) * Q ^ 2 / 2) := by
    rw [← hdiff]
    have h3 : (c - 2) * (1 / 2 - b ^ 2) * (r2 + r0) ≥ b * Q * (r2 - r0) * (r2 + r0) :=
      mul_le_mul_of_nonneg_right hneg.le (by positivity)
    have h4 : (c - 2) * (1 / 2 - b ^ 2) * (r2 + r0) ≤ (c - 2) * (1 / 2 - b ^ 2) * (2 * r2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  -- so `(1/2 - b²) · 4 r2 ≥ b Q³`, i.e. `(1/2 - b²) S ≥ Q³` with `S² = 17 - b²`
  have hk : (1 / 2 - b ^ 2) * (4 * r2) ≥ b * Q ^ 3 := by
    have := le_of_mul_le_mul_left (a := c - 2) (by nlinarith) hc2
    nlinarith
  have hsq : ((1 / 2 - b ^ 2) * (4 * r2)) ^ 2 ≥ (b * Q ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hk 2
  have hsq' : (1 / 2 - b ^ 2) ^ 2 * (17 - b ^ 2) ≥ (1 - b ^ 2) ^ 3 := by
    have e : ((1 / 2 - b ^ 2) * (4 * r2)) ^ 2 = b ^ 2 * ((1 / 2 - b ^ 2) ^ 2 * (17 - b ^ 2)) := by
      rw [mul_pow, mul_pow, hsq2]; ring
    have e' : (b * Q ^ 3) ^ 2 = b ^ 2 * (1 - b ^ 2) ^ 3 := by
      rw [mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hQ2]
    rw [e, e'] at hsq
    exact le_of_mul_le_mul_left hsq (by positivity)
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (sub_nonneg.2 h) hb2.le, mul_nonneg (mul_nonneg (sub_nonneg.2 h) hb2.le) hb2.le,
    mul_nonneg (mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h)) hb2.le]

theorem w2_mono {c b : ℝ} (hc : 2 ≤ c) (hb : 0 ≤ b) (hb1 : b ≤ 1) : w2 2 b ^ 2 ≤ w2 c b ^ 2 := by
  have h0 : 0 ≤ w2 2 b := by
    unfold w2; have : 0 ≤ 2 / 2 - (2 * b ^ 2 - 1) / 16 := by nlinarith
    positivity
  have h1 : w2 2 b ≤ w2 c b := by unfold w2; nlinarith
  exact pow_le_pow_left₀ h0 h1 2

/-- **L4.** If `D̂(c) ≤ 0`, then `I0(c) ≥ I0(2)`, given P4 at `c = 2`. -/
theorem I0_ge_two {c a b P Q : ℝ} (hc : 2 ≤ c) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb : 0 < b)
    (hb1 : b ≤ 1) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = 1 - b ^ 2)
    (hV : Vp c a b ≤ 0) (hD : Dh c b Q ≤ 0)
    (hP4 : b ^ 2 < 25 / 64 → W0 2 a b P + Dh 2 b Q ≤ 0) :
    I0 2 a b P Q ≤ I0 c a b P Q := by
  have hab : b ^ 2 ≤ a ^ 2 := by nlinarith
  have hV2 : Vp 2 a b ≤ 0 := le_trans (Vp_mono_c hc hab) hV
  have hV1 : Vp c 1 b ≤ 0 := le_trans (Vp_one_le hc ha ha2) hV
  have hcm2 := cm_pos le_rfl ha ha2 hb.le hb1 hP hP2 hV2
  have hW2 : 0 ≤ W0 2 a b P := by
    unfold W0; have := hcm2; positivity
  have hW := W0_step hc ha ha2 hb.le hb1 hP hP2 hQ2 hV
  have hw2 := mul_le_mul_of_nonneg_left (w2_mono hc hb.le hb1) (sq_nonneg Q)
  -- `D̂(c) - D̂(2) ≥ (c-2)(b² - 1/2)`
  have hDD : (c - 2) * (b ^ 2 - 1 / 2) ≤ Dh c b Q - Dh 2 b Q := by
    have hle : rr c 1 b ≤ rr 2 1 b := rr_le_two hc (by nlinarith)
    have : b * Q * rr c 1 b ≤ b * Q * rr 2 1 b := mul_le_mul_of_nonneg_left hle (by positivity)
    unfold Dh; unfold v22; nlinarith
  unfold I0
  rcases le_or_gt (Dh 2 b Q) (Dh c b Q) with hcase | hcase
  · -- `D̂` increased: direct comparison
    have e1 : Dh 2 b Q * W0 2 a b P ≤ Dh c b Q * W0 2 a b P :=
      mul_le_mul_of_nonneg_right hcase hW2
    have e2 : Dh c b Q * W0 2 a b P ≤ Dh c b Q * W0 c a b P :=
      mul_le_mul_of_nonpos_left (by nlinarith [sq_nonneg Q]) hD
    linarith
  · -- `D̂` decreased: then `b² < 25/64` and P4 applies
    have hsmall := b_small_of_Dh_lt hc hb hb1 hQ hQ2 hV1 hcase
    have hP4' := hP4 hsmall
    have e2 : Dh c b Q * (W0 2 a b P - (c - 2) * Q ^ 2 / 2) ≤ Dh c b Q * W0 c a b P :=
      mul_le_mul_of_nonpos_left hW hD
    have e3 : (c - 2) * (b ^ 2 - 1 / 2) * W0 2 a b P ≤ (Dh c b Q - Dh 2 b Q) * W0 2 a b P :=
      mul_le_mul_of_nonneg_right hDD hW2
    have hQ1 : Q ^ 2 ≤ 1 := by nlinarith
    have inner : 0 ≤ (b ^ 2 - 1 / 2) * W0 2 a b P - Q ^ 2 / 2 * Dh 2 b Q := by
      have e : (b ^ 2 - 1 / 2) * W0 2 a b P - Q ^ 2 / 2 * Dh 2 b Q =
          (b ^ 2 * W0 2 a b P + Q ^ 2 * -(W0 2 a b P + Dh 2 b Q)) / 2 := by rw [hQ2]; ring
      rw [e]
      have := mul_nonneg (sq_nonneg b) hW2
      have := mul_nonneg (sq_nonneg Q) (neg_nonneg.2 hP4')
      linarith
    have e4 := mul_nonneg (by linarith : (0:ℝ) ≤ c - 2) inner
    have e5 : Q ^ 2 / 2 * Dh c b Q * (c - 2) ≤ Q ^ 2 / 2 * Dh 2 b Q * (c - 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcase.le (by positivity))
        (by linarith)
    have e2' : Dh c b Q * W0 2 a b P - Dh c b Q * ((c - 2) * Q ^ 2 / 2) ≤ Dh c b Q * W0 c a b P := by
      rw [← mul_sub]; exact e2
    have e6 : Dh c b Q * ((c - 2) * Q ^ 2 / 2) = Q ^ 2 / 2 * Dh c b Q * (c - 2) := by ring
    have e7 : (c - 2) * ((b ^ 2 - 1 / 2) * W0 2 a b P - Q ^ 2 / 2 * Dh 2 b Q) =
        (c - 2) * (b ^ 2 - 1 / 2) * W0 2 a b P - Q ^ 2 / 2 * Dh 2 b Q * (c - 2) := by ring
    have e8 : (Dh c b Q - Dh 2 b Q) * W0 2 a b P = Dh c b Q * W0 2 a b P - Dh 2 b Q * W0 2 a b P := by
      ring
    linarith

/-! ## P4: `Ŵ0 = W0 + D̂ ≤ 0` at `c = 2` for `b² < 25/64` -/

/-- Dyadic upper bound for `D̂(2, 5/8)`, using `√41457 ≥ 203.609921`. -/
def Dhu : ℝ := -1015578365 / 2147483648

/-- The checker statement K1 (one-variable estimate at `b = 5/8`, radicals as box variables). -/
def K1Fact : Prop :=
  ∀ a P R : ℝ, 1 ≤ a → a ≤ 3 / 2 → 0 ≤ P → P ≤ 5 / 4 → 0 ≤ R → R ≤ 21 / 32 →
    P ^ 2 = a ^ 2 - 1 → R ^ 2 = -2 * Vp 2 a (5 / 8) →
    0 < -(P ^ 2 * w1 2 a ^ 2 + (v11 2 a - a * P * R) * (R ^ 2 + Dhu))

theorem Dh_two_eq {b Q : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hQ : 0 ≤ Q) :
    Dh 2 b Q = (-17 + 40 * b ^ 2 - 8 * b ^ 4 - 4 * b ^ 2 * (Q * Real.sqrt (17 - b ^ 2))) / 16 := by
  have hr : rr 2 1 b = b * Real.sqrt (17 - b ^ 2) / 4 := by
    unfold rr
    rw [show -2 * Vp 2 1 b = (b / 4) ^ 2 * (17 - b ^ 2) by unfold Vp; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  unfold Dh v22; rw [hr]; ring

theorem Dh_two_le {b Q : ℝ} (hb : 0 < b) (hb2 : b ^ 2 < 25 / 64) (hQ : 0 ≤ Q)
    (hQ2 : Q ^ 2 = 1 - b ^ 2) : Dh 2 b Q ≤ Dhu := by
  have hb1 : b ≤ 1 := by nlinarith
  rw [Dh_two_eq hb.le hb1 hQ]
  set σ := Q * Real.sqrt (17 - b ^ 2) with hσ
  have hS : Real.sqrt (17 - b ^ 2) ^ 2 = 17 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hσ0 : 0 ≤ σ := by positivity
  have hσ2 : σ ^ 2 = (1 - b ^ 2) * (17 - b ^ 2) := by rw [hσ, mul_pow, hS, hQ2]
  have hσ_hi : σ ≤ 33 / 8 := by nlinarith
  -- `σ ≥ 203.609921/64` since `σ² ≥ 41457/4096`
  have hσ_lo : 203609921 / 1000000 / 64 ≤ σ := by
    have : (203609921 / 1000000 / 64 : ℝ) ^ 2 ≤ σ ^ 2 := by rw [hσ2]; nlinarith
    exact abs_le_of_sq_le_sq' this hσ0 |>.2
  unfold Dhu
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 25 / 64 - b ^ 2) hσ0,
    mul_nonneg (by linarith : (0:ℝ) ≤ 25 / 64 - b ^ 2) (by linarith : (0:ℝ) ≤ 33 / 8 - σ),
    mul_nonneg (by linarith : (0:ℝ) ≤ 25 / 64 - b ^ 2) (sq_nonneg b)]

theorem P4 (hK1 : K1Fact) {a b P Q : ℝ} (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb : 0 < b)
    (hb2 : b ^ 2 < 25 / 64) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hQ : 0 ≤ Q)
    (hQ2 : Q ^ 2 = 1 - b ^ 2) (hV : Vp 2 a b ≤ 0) : W0 2 a b P + Dh 2 b Q ≤ 0 := by
  have hb58 : b ≤ 5 / 8 := by nlinarith
  have hV58 : Vp 2 a (5 / 8) ≤ 0 := le_trans (Vp_anti_b le_rfl hb.le hb58 (by norm_num)) hV
  have ha32 : a ≤ 3 / 2 := by
    by_contra h; push Not at h
    unfold Vp at hV58
    have h1 : 0 < a - 3 / 2 := by linarith
    have h2 : 0 ≤ 2 - a := by linarith
    nlinarith [mul_nonneg h1.le h2, mul_nonneg (mul_nonneg h1.le h2) h1.le,
      mul_nonneg (mul_nonneg h1.le h2) (by linarith : (0:ℝ) ≤ a), mul_pos h1 h1,
      mul_pos (mul_pos h1 h1) h1]
  set R := rr 2 a (5 / 8) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = -2 * Vp 2 a (5 / 8) := rr_sq hV58
  have hR12 : R ≤ 21 / 32 := by
    have : R ^ 2 ≤ (21 / 32) ^ 2 := by
      rw [hR2]
      have h1 := Vp_one_le (b := 5 / 8) (le_refl (2:ℝ)) ha (by linarith)
      have h2 : Vp 2 1 (5 / 8) = -26575 / 131072 := by unfold Vp; norm_num
      linarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |>.2
  have hP65 : P ≤ 5 / 4 := by
    have : P ^ 2 ≤ (5 / 4) ^ 2 := by rw [hP2]; nlinarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |>.2
  have hk := hK1 a P R ha ha32 hP hP65 hR0 hR12 hP2 hR2
  -- monotonicity in `b`
  have hrb : rr 2 a b ≤ R :=
    Real.sqrt_le_sqrt (by linarith [Vp_anti_b (a := a) le_rfl hb.le hb58 (by norm_num)])
  have hcm58 := cm_pos le_rfl ha ha2 (by norm_num : (0:ℝ) ≤ 5 / 8) (by norm_num) hP hP2 hV58
  have hcmb : cm 2 a (5 / 8) P ≤ cm 2 a b P := by
    unfold cm; rw [← hR]
    have := mul_le_mul_of_nonneg_left hrb (by positivity : (0:ℝ) ≤ a * P); linarith
  have hW : W0 2 a b P ≤ P ^ 2 * w1 2 a ^ 2 / cm 2 a (5 / 8) P + R ^ 2 := by
    unfold W0
    have h1 : P ^ 2 * w1 2 a ^ 2 / cm 2 a b P ≤ P ^ 2 * w1 2 a ^ 2 / cm 2 a (5 / 8) P :=
      div_le_div_of_nonneg_left (by positivity) hcm58 hcmb
    have h2 : rr 2 a b ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrb 2
    linarith
  have hD := Dh_two_le hb hb2 hQ hQ2
  have hcmR : cm 2 a (5 / 8) P = v11 2 a - a * P * R := by unfold cm; rw [hR]
  have hfin : P ^ 2 * w1 2 a ^ 2 / cm 2 a (5 / 8) P + R ^ 2 + Dhu < 0 := by
    have e : P ^ 2 * w1 2 a ^ 2 / cm 2 a (5 / 8) P + R ^ 2 + Dhu =
        (P ^ 2 * w1 2 a ^ 2 + cm 2 a (5 / 8) P * (R ^ 2 + Dhu)) / cm 2 a (5 / 8) P := by
      have := hcm58.ne'
      field_simp
      ring
    rw [e]
    apply div_neg_of_neg_of_pos _ hcm58
    rw [hcmR]; linarith
  linarith

/-! ## L5: Liu--Salomão Lemma 9.7 at `c = 2` -/

/-- The radicand of `j₂`. -/
def jrad (b t : ℝ) : ℝ :=
  (2 + (t ^ 2 * b ^ 2)) * (17 - 14 * t ^ 2 - b ^ 2 - 11 * t ^ 4 * b ^ 2 + 4 * t ^ 6 * b ^ 4 + t ^ 8 * b ^ 6)

/-- `16 D` (Liu--Salomão (9.13)), with `s = √((1-b²)(17-b²))`. -/
def D16 (b s : ℝ) : ℝ := -17 - 8 * b ^ 4 + 40 * b ^ 2 - 4 * b ^ 2 * s

/-- `256 E₁` (Liu--Salomão (9.15)), with `J = j₂`. -/
def E1x256 (b t J s : ℝ) : ℝ :=
  16 * (85 - 26 * b ^ 2 + b ^ 4 - (17 - b ^ 2) * s) *
      ((7 + 40 * (t ^ 2 * b ^ 2) - 8 * (t ^ 2 * b ^ 2) ^ 2 - 32 * (t ^ 2 * b ^ 2) ^ 3 - 8 * (t ^ 2 * b ^ 2) ^ 4) - 4 * t * b ^ 2 * (1 + (t ^ 2 * b ^ 2)) * J) -
    16 * t ^ 3 * D16 b s * ((-14 + 3 * (t ^ 2 * b ^ 2) + (t ^ 2 * b ^ 2) ^ 2) * (1 + (t ^ 2 * b ^ 2)) ^ 2 * J +
      t * (70 + 18 * (t ^ 2 * b ^ 2) - 105 * (t ^ 2 * b ^ 2) ^ 2 - 74 * (t ^ 2 * b ^ 2) ^ 3 + 2 * (t ^ 2 * b ^ 2) ^ 4 + 8 * (t ^ 2 * b ^ 2) ^ 5 + (t ^ 2 * b ^ 2) ^ 6))

/-- The checker statement K2 (`E₁ > 0`, radicals `J = j₂` as a box variable). -/
def K2Fact : Prop :=
  ∀ b t J s : ℝ, 0 ≤ b → b ≤ 1 → 0 ≤ t → t ≤ 5 / 4 → 0 ≤ J → J ≤ 8 → 0 < s →
    s ^ 2 = (1 - b ^ 2) * (17 - b ^ 2) → J ^ 2 = jrad b t → 0 ≤ -D16 b s → 0 ≤ 17 - 14 * t ^ 2 →
    t ^ 2 * b ^ 2 ≤ 1 → 0 < E1x256 b t J s

/-- `256 E₁` in the low-degree variables `l = b²`, `x = t² b²`. -/
def E1x (l t x J s : ℝ) : ℝ :=
  16 * (85 - 26 * l + l ^ 2 - (17 - l) * s) *
      ((7 + 40 * x - 8 * x ^ 2 - 32 * x ^ 3 - 8 * x ^ 4) - 4 * t * l * (1 + x) * J) -
    16 * t ^ 3 * (-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) * ((-14 + 3 * x + x ^ 2) * (1 + x) ^ 2 * J +
      t * (70 + 18 * x - 105 * x ^ 2 - 74 * x ^ 3 + 2 * x ^ 4 + 8 * x ^ 5 + x ^ 6))

/-- The checker statement K2 in the variables `(l, t, x, J)` with `r = s`. -/
def K2xFact : Prop :=
  ∀ l t x J s : ℝ, 0 ≤ l → l ≤ 1 → 0 ≤ t → t ≤ 5 / 4 → 0 ≤ x → x ≤ 1 → 0 ≤ J → J ≤ 8 → 0 < s →
    s ^ 2 = (1 - l) * (17 - l) → x = t ^ 2 * l →
    J ^ 2 = (2 + x) * (17 - 14 * t ^ 2 - l - 11 * t ^ 2 * x + 4 * t ^ 2 * x ^ 2 + t ^ 2 * x ^ 3) →
    0 ≤ -(-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) → 0 ≤ 17 - 14 * t ^ 2 →
    0 < E1x l t x J s

theorem K2Fact_of_K2x (h : K2xFact) : K2Fact := by
  intro b t J s hb0 hb1 ht0 ht1 hJ0 hJ1 hs hs2 hJ2 hD ht hx1
  have hl1 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
  have hD' : 0 ≤ -(-17 - 8 * (b ^ 2) ^ 2 + 40 * b ^ 2 - 4 * b ^ 2 * s) := by
    unfold D16 at hD; ring_nf; ring_nf at hD; linarith
  have key := h (b ^ 2) t (t ^ 2 * b ^ 2) J s (sq_nonneg b) hl1 ht0 ht1 (by positivity) hx1 hJ0 hJ1 hs
    hs2 (by ring) (by rw [hJ2]; unfold jrad; ring) hD' ht
  convert key using 1
  unfold E1x256 E1x D16; ring

/-- Liu--Salomão's polynomial upper bound `j₂,₀` for `j₂` (Lemma 9.8(iii)), with `x = t² l`. -/
def j20 (l t x : ℝ) : ℝ := 169 / 32 - (t ^ 2 - 1 / 4) * (5 / 2 + l / 4 + t ^ 2) - t ^ 2 * x / 2

/-- Checker statement K2y: `E₁` with `J` replaced by `j₂,₀`. -/
def K2yFact : Prop :=
  ∀ l t x s : ℝ, 0 ≤ l → l ≤ 1 → 0 ≤ t → t ≤ 5 / 4 → 0 ≤ x → x ≤ 1 → 0 < s →
    s ^ 2 = (1 - l) * (17 - l) → x = t ^ 2 * l →
    0 ≤ -(-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) → 0 ≤ 17 - 14 * t ^ 2 →
    0 < E1x l t x (j20 l t x) s

/-- Checker statement K3: `0 < j₂,₀` and `j₂² < j₂,₀²`. -/
def K3Fact : Prop :=
  ∀ l t : ℝ, 0 ≤ l → l ≤ 1 → 0 ≤ t → t ≤ 5 / 4 → 0 ≤ 17 - 14 * t ^ 2 → 0 ≤ 1 - t ^ 2 * l →
    0 < j20 l t (t ^ 2 * l) ∧
    0 < j20 l t (t ^ 2 * l) ^ 2 - (2 + t ^ 2 * l) * (17 - 14 * t ^ 2 - l - 11 * t ^ 2 * (t ^ 2 * l) +
      4 * t ^ 2 * (t ^ 2 * l) ^ 2 + t ^ 2 * (t ^ 2 * l) ^ 3)

theorem j1_nonneg {l s : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = (1 - l) * (17 - l)) : 0 ≤ 85 - 26 * l + l ^ 2 - (17 - l) * s := by
  have h0 : 0 ≤ 85 - 26 * l + l ^ 2 := by nlinarith
  have hsq : ((17 - l) * s) ^ 2 ≤ (85 - 26 * l + l ^ 2) ^ 2 := by
    rw [mul_pow, hs2]
    nlinarith [mul_nonneg hl0 (sub_nonneg.2 hl1), mul_nonneg (mul_nonneg hl0 hl0) (sub_nonneg.2 hl1),
      mul_nonneg (mul_nonneg hl0 hl0) hl0, mul_nonneg (mul_nonneg hl0 hl0) (mul_nonneg hl0 hl0)]
  have := abs_le_of_sq_le_sq' hsq h0
  linarith [this.2]

theorem K2xFact_of (hy : K2yFact) (h3 : K3Fact) : K2xFact := by
  intro l t x J s hl0 hl1 ht0 ht1 hx0 hx1 hJ0 hJ1 hs hs2 hx hJ2 hD ht
  obtain ⟨hj0, hj2⟩ := h3 l t hl0 hl1 ht0 ht1 ht (by rw [← hx]; linarith)
  rw [← hx] at hj0 hj2
  have hJle : J ≤ j20 l t x := by
    have : J ^ 2 ≤ j20 l t x ^ 2 := by rw [hJ2]; linarith
    exact (abs_le_of_sq_le_sq' this hj0.le).2
  have hy' := hy l t x s hl0 hl1 ht0 ht1 hx0 hx1 hs hs2 hx hD ht
  have hj1 := j1_nonneg hl0 hl1 hs.le hs2
  have hj3 : (-14 + 3 * x + x ^ 2) * (1 + x) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  -- the coefficient of `J` in `E₁` is `≤ 0`
  set cJ := -64 * t * l * (1 + x) * (85 - 26 * l + l ^ 2 - (17 - l) * s) -
    16 * t ^ 3 * (-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) * ((-14 + 3 * x + x ^ 2) * (1 + x) ^ 2) with hcJ
  have hcJ0 : cJ ≤ 0 := by
    have h1 : 0 ≤ 64 * t * l * (1 + x) * (85 - 26 * l + l ^ 2 - (17 - l) * s) := by positivity
    have h2 : 0 ≤ (-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) * ((-14 + 3 * x + x ^ 2) * (1 + x) ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hj3
    have h3 : 0 ≤ 16 * t ^ 3 * ((-17 - 8 * l ^ 2 + 40 * l - 4 * l * s) * ((-14 + 3 * x + x ^ 2) * (1 + x) ^ 2)) := by
      positivity
    rw [hcJ]; nlinarith
  have hdiff : E1x l t x J s - E1x l t x (j20 l t x) s = cJ * (J - j20 l t x) := by
    rw [hcJ]; unfold E1x; ring
  have : 0 ≤ cJ * (J - j20 l t x) := mul_nonneg_of_nonpos_of_nonpos hcJ0 (by linarith)
  linarith

/-- Liu--Salomão (9.14): `64 · cmin · I0 = b⁴ E₁` in the coordinates `a = 1 + t² b²`. -/
theorem key_identity (b t J s : ℝ) :
    16384 * ((v11 2 (1 + (t ^ 2 * b ^ 2)) - (1 + (t ^ 2 * b ^ 2)) * (t * b ^ 2 * J / 4)) * (1 - b ^ 2) * w2 2 b ^ 2 +
      D16 b s / 16 * ((t ^ 2 * b ^ 2) * (2 + (t ^ 2 * b ^ 2)) * w1 2 (1 + (t ^ 2 * b ^ 2)) ^ 2 +
        (v11 2 (1 + (t ^ 2 * b ^ 2)) - (1 + (t ^ 2 * b ^ 2)) * (t * b ^ 2 * J / 4)) *
          (b ^ 2 * (17 - 14 * t ^ 2 - b ^ 2 - 11 * t ^ 4 * b ^ 2 + 4 * t ^ 6 * b ^ 4 + t ^ 8 * b ^ 6) / 16)))
      = b ^ 4 * E1x256 b t J s := by
  unfold v11 w1 w2 E1x256 D16; ring

theorem I0_two_pos (hK2 : K2Fact) {a b P Q : ℝ} (ha : 1 ≤ a) (ha2 : a ≤ 2) (hb : 0 < b)
    (hb1 : b ≤ 1) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1) (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = 1 - b ^ 2)
    (hV : Vp 2 a b ≤ 0) : 0 < I0 2 a b P Q := by
  have hcm := cm_pos le_rfl ha ha2 hb.le hb1 hP hP2 hV
  have hW0 : 0 ≤ W0 2 a b P := by unfold W0; positivity
  set S := Real.sqrt (17 - b ^ 2) with hS
  have hS2 : S ^ 2 = 17 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hDh := Dh_two_eq hb.le hb1 hQ
  rw [← hS] at hDh
  rcases le_or_gt 0 (Dh 2 b Q) with hD | hD
  · -- `D̂ ≥ 0`
    rcases hb1.lt_or_eq with hb1' | hb1'
    · have hQp : 0 < Q := by
        rcases hQ.lt_or_eq with h | h
        · exact h
        · rw [← h] at hQ2; nlinarith
      have := w2_pos le_rfl hb hb1
      unfold I0
      have : 0 < Q ^ 2 * w2 2 b ^ 2 := by positivity
      have : 0 ≤ Dh 2 b Q * W0 2 a b P := mul_nonneg hD hW0
      linarith
    · subst hb1'
      have hQ0 : Q = 0 := by nlinarith
      have hDp : 0 < Dh 2 1 Q := by rw [hDh, hQ0]; norm_num
      have hWp : 0 < W0 2 a 1 P := by
        unfold W0
        rcases hP.lt_or_eq with hP' | hP'
        · have := w1_pos le_rfl ha ha2
          have : 0 < P ^ 2 * w1 2 a ^ 2 / cm 2 a 1 P := by positivity
          positivity
        · have ha1 : a = 1 := by nlinarith
          subst ha1
          rw [rr_sq hV]; unfold Vp; norm_num
          positivity
      unfold I0
      have := mul_pos hDp hWp
      positivity
  · -- `D̂ < 0`: the coordinates `(b, t)` with `a = 1 + t² b²`
    have hb1' : b < 1 := by
      rcases hb1.lt_or_eq with h | h
      · exact h
      · subst h
        have hQ0 : Q = 0 := by nlinarith
        rw [hDh, hQ0] at hD; norm_num at hD
    have hQp : 0 < Q := by
      rcases hQ.lt_or_eq with h | h
      · exact h
      · rw [← h] at hQ2; nlinarith
    set x := a - 1 with hx
    have hx0 : 0 ≤ x := by linarith
    have hx1 : x ≤ 1 := by linarith
    set t := Real.sqrt x / b with ht
    have ht0 : 0 ≤ t := by positivity
    have htb : t ^ 2 * b ^ 2 = x := by
      rw [ht, div_pow, Real.sq_sqrt hx0]; field_simp
    have ha_eq : a = 1 + (t ^ 2 * b ^ 2) := by rw [htb]; ring
    -- `P = t b √(2 + x)`
    set U := Real.sqrt (2 + (t ^ 2 * b ^ 2)) with hU
    have hU2 : U ^ 2 = 2 + (t ^ 2 * b ^ 2) := Real.sq_sqrt (by positivity)
    have hU0 : 0 ≤ U := Real.sqrt_nonneg _
    have hPe : P = t * b * U := by
      have h1 : P ^ 2 = (t * b * U) ^ 2 := by rw [hP2, mul_pow, hU2, ha_eq]; ring
      exact (pow_left_inj₀ hP (by positivity) two_ne_zero).1 h1
    -- `r = b √Rt / 4`
    set Rt := 17 - 14 * t ^ 2 - b ^ 2 - 11 * t ^ 4 * b ^ 2 + 4 * t ^ 6 * b ^ 4 + t ^ 8 * b ^ 6 with hRt
    have hVR : -2 * Vp 2 a b = b ^ 2 * Rt / 16 := by rw [ha_eq, hRt]; unfold Vp; ring
    have hRt0 : 0 ≤ Rt := by
      have h1 : 0 ≤ b ^ 2 * Rt := by linarith
      by_contra h; push Not at h; nlinarith [mul_pos (pow_pos hb 2) (neg_pos.2 h)]
    set J := Real.sqrt (jrad b t) with hJ
    have hJ2 : J ^ 2 = jrad b t := Real.sq_sqrt (by unfold jrad; rw [← hRt]; positivity)
    have hJ0 : 0 ≤ J := Real.sqrt_nonneg _
    have hr : rr 2 a b = b * Real.sqrt Rt / 4 := by
      unfold rr; rw [hVR, show b ^ 2 * Rt / 16 = (b / 4) ^ 2 * Rt by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]; ring
    have hPr : P * rr 2 a b = t * b ^ 2 * J / 4 := by
      rw [hPe, hr, hU, hJ]
      have : jrad b t = (2 + (t ^ 2 * b ^ 2)) * Rt := by unfold jrad; rw [hRt]
      rw [this, Real.sqrt_mul (by positivity)]; ring
    -- bounds for the checker
    have hpoly : 0 ≤ 11 * x - 4 * x ^ 2 - x ^ 3 := by nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - x)]
    have hRt_eq : Rt = 17 - b ^ 2 - t ^ 2 * (14 + 11 * x - 4 * x ^ 2 - x ^ 3) := by
      rw [hRt, ← htb]; ring
    have htp := mul_nonneg (sq_nonneg t) hpoly
    have ht17 : 0 ≤ 17 - 14 * t ^ 2 := by
      have e : 17 - 14 * t ^ 2 = Rt + b ^ 2 + t ^ 2 * (11 * x - 4 * x ^ 2 - x ^ 3) := by
        rw [hRt_eq]; ring
      rw [e]; have := sq_nonneg b; linarith
    have ht54 : t ≤ 5 / 4 := by
      have : t ^ 2 ≤ (5 / 4) ^ 2 := by linarith
      exact abs_le_of_sq_le_sq' this (by norm_num) |>.2
    have hJ8 : J ≤ 8 := by
      have h1 : Rt ≤ 17 := by
        have e : Rt = 17 - b ^ 2 - 14 * t ^ 2 - t ^ 2 * (11 * x - 4 * x ^ 2 - x ^ 3) := by
          rw [hRt_eq]; ring
        rw [e]; have := sq_nonneg b; have := sq_nonneg t; linarith
      have h2 : (2 + x) * Rt ≤ 3 * 17 :=
        mul_le_mul (by linarith) h1 hRt0 (by norm_num)
      have : J ^ 2 ≤ 8 ^ 2 := by
        rw [hJ2]
        have e : jrad b t = (2 + x) * Rt := by unfold jrad; rw [hRt, htb]
        rw [e]; linarith
      exact abs_le_of_sq_le_sq' this (by norm_num) |>.2
    set s := Q * S with hs
    have hb21 : b ^ 2 ≤ 1 := pow_le_one₀ hb.le hb1
    have hs0 : 0 < s := by
      have : 0 < S := Real.sqrt_pos.2 (by linarith)
      exact mul_pos hQp this
    have hs2 : s ^ 2 = (1 - b ^ 2) * (17 - b ^ 2) := by rw [hs, mul_pow, hS2, hQ2]
    have hDs : Dh 2 b Q = D16 b s / 16 := by rw [hDh]; unfold D16; rw [hs]; ring
    have hD16 : 0 ≤ -D16 b s := by rw [hDs] at hD; linarith
    have hE := hK2 b t J s hb.le hb1 ht0 ht54 hJ0 hJ8 hs0 hs2 hJ2 hD16 ht17 (by rw [htb]; exact hx1)
    -- the identity
    have hcmE : cm 2 a b P = v11 2 (1 + (t ^ 2 * b ^ 2)) - (1 + (t ^ 2 * b ^ 2)) * (t * b ^ 2 * J / 4) := by
      unfold cm; rw [mul_assoc, hPr, ← ha_eq]
    have hI0 : cm 2 a b P * I0 2 a b P Q = cm 2 a b P * Q ^ 2 * w2 2 b ^ 2 +
        Dh 2 b Q * (P ^ 2 * w1 2 a ^ 2 + cm 2 a b P * rr 2 a b ^ 2) := by
      unfold I0 W0
      have hne := hcm.ne'
      field_simp
    have hI : 16384 * (cm 2 a b P * I0 2 a b P Q) = b ^ 4 * E1x256 b t J s := by
      rw [hI0, rr_sq hV, hVR, hDs, hQ2, hP2, hcmE, ha_eq, hRt]
      linear_combination key_identity b t J s
    have : 0 < cm 2 a b P * I0 2 a b P Q := by
      have := mul_pos (pow_pos hb 4) hE
      linarith
    exact pos_of_mul_pos_right this hcm.le

/-! ## Assembly -/

theorem corner_alg (hK1 : K1Fact) (hK2 : K2Fact) {c a b P Q σ τ : ℝ} (hc : 2 ≤ c) (hb' : 0 < b) (ha : 1 ≤ a)
    (h0 : a ^ 2 ≤ 2 * c) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hP : 0 ≤ P) (hP2 : P ^ 2 = a ^ 2 - 1)
    (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = 1 - b ^ 2) (hV : Vp c a b ≤ 0) (hσ : σ = 1 ∨ σ = -1)
    (hτ : τ = 1 ∨ τ = -1) :
    0 < rr c a b ^ 2 * (v11 c a + σ * a * P * rr c a b) * (v22 c b + τ * b * Q * rr c a b) +
      (v11 c a + σ * a * P * rr c a b) * (Q * w2 c b) ^ 2 +
      (v22 c b + τ * b * Q * rr c a b) * (P * w1 c a) ^ 2 := by
  have ha2 := a_le_two_of_hill hc ha h0 hb0 hb1 hV
  have hb := hb'
  have hV2 : Vp 2 a b ≤ 0 := le_trans (Vp_mono_c hc (by nlinarith)) hV
  refine corner_of_I0 hc hb' ha ha2 hb0 hb1 hP hP2 hQ hQ2 hV hσ hτ (fun hD => ?_)
  have h2 := I0_two_pos hK2 ha ha2 hb hb1 hP hP2 hQ hQ2 hV2
  have hge := I0_ge_two hc ha ha2 hb hb1 hP hP2 hQ hQ2 hV hD.le
    (fun hb2 => P4 hK1 ha ha2 hb hb2 hP hP2 hQ hQ2 hV2)
  linarith

theorem corner_trig (hK1 : K1Fact) (hK2 : K2Fact) (c x₁ x₂ σ τ : ℝ) (hc : 2 ≤ c) (hb' : 0 < Real.cos x₂)
    (h1 : |x₂| ≤ Real.pi / 2) (h0 : Real.cosh x₁ ^ 2 ≤ 2 * c)
    (hV : c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128 ≤ 0)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    let V := c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128
    let V₁ := c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
      Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32
    let V₂ := c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32
    let V₁₁ := c * Real.cosh (2 * x₁) / 2 - Real.cosh x₁ / 2 - Real.cosh (4 * x₁) / 16
    let V₂₂ := c * Real.cos (2 * x₂) / 2 - Real.cos (4 * x₂) / 16
    let r := Real.sqrt (-2 * V)
    let cc := V₁₁ + σ * r * |Real.sinh (2 * x₁)| / 2
    let dd := V₂₂ + τ * r * |Real.sin (2 * x₂)| / 2
    0 < r ^ 2 * cc * dd + cc * V₂ ^ 2 + dd * V₁ ^ 2 := by
  intro V V₁ V₂ V₁₁ V₂₂ r cc dd
  have hsh : Real.sinh x₁ ^ 2 = Real.cosh x₁ ^ 2 - 1 := by rw [Real.cosh_sq]; ring
  have hsn : Real.sin x₂ ^ 2 = 1 - Real.cos x₂ ^ 2 := Real.sin_sq x₂
  have hc2 : Real.cosh (2 * x₁) = 2 * Real.cosh x₁ ^ 2 - 1 := by
    rw [Real.cosh_two_mul, hsh]; ring
  have hcs2 : Real.cos (2 * x₂) = 2 * Real.cos x₂ ^ 2 - 1 := Real.cos_two_mul x₂
  have hVe : V = Vp c (Real.cosh x₁) (Real.cos x₂) := by
    show c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128 = _
    rw [Real.sinh_two_mul, Real.sin_two_mul]
    unfold Vp
    have e1 : (2 * Real.sinh x₁ * Real.cosh x₁) ^ 2 = 4 * Real.sinh x₁ ^ 2 * Real.cosh x₁ ^ 2 := by ring
    have e2 : (2 * Real.sin x₂ * Real.cos x₂) ^ 2 = 4 * Real.sin x₂ ^ 2 * Real.cos x₂ ^ 2 := by ring
    rw [e1, e2, hsh, hsn]; ring
  have hre : r = rr c (Real.cosh x₁) (Real.cos x₂) := by
    show Real.sqrt (-2 * V) = _; rw [hVe]; rfl
  have habs1 : |Real.sinh (2 * x₁)| / 2 = Real.cosh x₁ * |Real.sinh x₁| := by
    rw [Real.sinh_two_mul, abs_mul, abs_mul, abs_two, abs_of_pos (Real.cosh_pos x₁)]; ring
  have hb0 : 0 ≤ Real.cos x₂ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le x₂], by linarith [le_abs_self x₂]⟩
  have habs2 : |Real.sin (2 * x₂)| / 2 = Real.cos x₂ * |Real.sin x₂| := by
    rw [Real.sin_two_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hb0]; ring
  have hcce : cc = v11 c (Real.cosh x₁) + σ * Real.cosh x₁ * |Real.sinh x₁| * rr c (Real.cosh x₁) (Real.cos x₂) := by
    show V₁₁ + σ * r * |Real.sinh (2 * x₁)| / 2 = _
    rw [mul_div_assoc, habs1, hre]
    show c * Real.cosh (2 * x₁) / 2 - Real.cosh x₁ / 2 - Real.cosh (4 * x₁) / 16 + _ = _
    rw [show (4 : ℝ) * x₁ = 2 * (2 * x₁) by ring, Real.cosh_two_mul (2 * x₁), Real.sinh_sq, hc2]
    unfold v11; ring
  have hdde : dd = v22 c (Real.cos x₂) + τ * Real.cos x₂ * |Real.sin x₂| * rr c (Real.cosh x₁) (Real.cos x₂) := by
    show V₂₂ + τ * r * |Real.sin (2 * x₂)| / 2 = _
    rw [mul_div_assoc, habs2, hre]
    show c * Real.cos (2 * x₂) / 2 - Real.cos (4 * x₂) / 16 + _ = _
    rw [show (4 : ℝ) * x₂ = 2 * (2 * x₂) by ring, Real.cos_two_mul (2 * x₂), hcs2]
    unfold v22; ring
  have hV1e : V₁ ^ 2 = (|Real.sinh x₁| * w1 c (Real.cosh x₁)) ^ 2 := by
    show (c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
      Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32) ^ 2 = _
    rw [mul_pow, sq_abs, Real.sinh_two_mul, hc2]
    unfold w1; ring
  have hV2e : V₂ ^ 2 = (|Real.sin x₂| * w2 c (Real.cos x₂)) ^ 2 := by
    show (c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32) ^ 2 = _
    rw [mul_pow, sq_abs, Real.sin_two_mul, hcs2]
    unfold w2; ring
  rw [hre, hcce, hdde, hV1e, hV2e]
  have hV' : Vp c (Real.cosh x₁) (Real.cos x₂) ≤ 0 := by rw [← hVe]; exact hV
  exact corner_alg hK1 hK2 hc hb' (Real.one_le_cosh x₁) h0 hb0 (Real.cos_le_one x₂) (abs_nonneg _)
    (by rw [sq_abs, hsh]) (abs_nonneg _) (by rw [sq_abs, hsn]) hV' hσ hτ

end

end BirkhoffGlobalSection.EHConvex.Corner

namespace BirkhoffGlobalSection.TangentialHessian.Checker.Data

set_option maxRecDepth 100000

theorem cornerK1_check : check NP.centredEnc cornerK1 = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_00
  obtain ⟨h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_01
  show checkTree NP.centredEnc cornerK1 cornerK1_tree cornerK1_box = true
  simp only [cornerK1_tree, checkTree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, Bool.and_self]

theorem cornerK2y_check : check NP.centredEnc cornerK2y = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_02
  obtain ⟨h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_03
  obtain ⟨h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_04
  obtain ⟨h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_05
  obtain ⟨h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_06
  obtain ⟨h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_07
  obtain ⟨h73, h74, h75, h76, h77⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_08
  show checkTree NP.centredEnc cornerK2y cornerK2y_tree cornerK2y_box = true
  simp only [cornerK2y_tree, checkTree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, Bool.and_self]

theorem cornerK3_check : check NP.centredEnc cornerK3 = true := by
  obtain ⟨h0, h1⟩ := BirkhoffGlobalSection.EHConvex.corner_cert_part_09
  show checkTree NP.centredEnc cornerK3 cornerK3_tree cornerK3_box = true
  simp only [cornerK3_tree, checkTree, h0, h1, Bool.and_self]

end BirkhoffGlobalSection.TangentialHessian.Checker.Data

/-! From the checker certificates `cornerK1`, `cornerK2` to `K1Fact`, `K2Fact`. -/

namespace BirkhoffGlobalSection.EHConvex.Corner

open BirkhoffGlobalSection.TangentialHessian

set_option maxRecDepth 100000

theorem flat_eval (n : ℕ) (p : Checker.Poly Checker.Dy) (x : List ℝ) (h : x.length = n) :
    Checker.NP.DPoly.eval (⟨n, Checker.NP.ofFlat n p⟩ : Checker.NP.DPoly Checker.Dy) x =
      Checker.evalR p x := Checker.NP.eval_ofFlat n p x h

theorem K1Fact_of_check (hc : Checker.check Checker.NP.centredEnc Checker.Data.cornerK1 = true) :
    K1Fact := by
  intro a P R ha1 ha2 hP0 hP1 hR0 hR1 hP2 hR2
  have hx : Checker.InBox [a, P, R] Checker.Data.cornerK1.box := by
    clear hc
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) <;>
    · unfold Checker.Mem; simp only [Checker.Dy.cnum_toReal_mk]
      constructor <;> norm_num <;> linarith
  have hr2' : (1:ℝ) ^ 2 = Checker.NP.DPoly.eval Checker.Data.cornerK1.rSq [a, P, R] := by
    clear hc
    show (1:ℝ) ^ 2 = Checker.NP.DPoly.eval ⟨3, Checker.NP.ofFlat 3 Checker.Data.cornerK1_rSq⟩ _
    rw [flat_eval 3 _ _ rfl]
    simp [Checker.Data.cornerK1_rSq, Checker.evalR, Checker.monoR]
  have hhyp : ∀ p ∈ Checker.Data.cornerK1.hyps,
      0 ≤ Checker.NP.DPoly.eval p ([a, P, R] ++ [1]) := by
    clear hc
    intro p hp
    simp only [Checker.Data.cornerK1, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [flat_eval 4 q _ rfl]
    simp only [Checker.Data.cornerK1_hyps, List.mem_cons, List.not_mem_nil, or_false] at hq
    unfold Vp at hR2
    rcases hq with rfl | rfl | rfl | rfl <;>
    · simp [Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]; nlinarith
  have hg := Checker.check_sound Checker.NP.centredEnc_sound Checker.Data.cornerK1 hc _ hx 1
    one_pos hr2' hhyp
  have hE := hg _ (List.mem_map_of_mem List.mem_cons_self)
  rw [flat_eval 4 _ _ rfl] at hE
  convert hE using 1
  simp [Checker.Data.cornerK1_goals, Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]
  unfold w1 v11 Dhu; ring

theorem K2yFact_of_check (hc : Checker.check Checker.NP.centredEnc Checker.Data.cornerK2y = true) :
    K2yFact := by
  intro l t x s hl0 hl1 ht0 ht1 hx0 hx1 hs hs2 hx hD ht
  have hX : Checker.InBox [l, t, x] Checker.Data.cornerK2y.box := by
    clear hc
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) <;>
    · unfold Checker.Mem; simp only [Checker.Dy.cnum_toReal_mk]
      constructor <;> norm_num <;> linarith
  have hr2' : s ^ 2 = Checker.NP.DPoly.eval Checker.Data.cornerK2y.rSq [l, t, x] := by
    clear hc
    show s ^ 2 = Checker.NP.DPoly.eval ⟨3, Checker.NP.ofFlat 3 Checker.Data.cornerK2y_rSq⟩ _
    rw [flat_eval 3 _ _ rfl, hs2]
    simp [Checker.Data.cornerK2y_rSq, Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]; ring
  have hhyp : ∀ p ∈ Checker.Data.cornerK2y.hyps,
      0 ≤ Checker.NP.DPoly.eval p ([l, t, x] ++ [s]) := by
    clear hc
    intro p hp
    simp only [Checker.Data.cornerK2y, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [flat_eval 4 q _ rfl]
    simp only [Checker.Data.cornerK2y_hyps, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
    · simp [Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]; nlinarith
  have hg := Checker.check_sound Checker.NP.centredEnc_sound Checker.Data.cornerK2y hc _ hX s
    hs hr2' hhyp
  have hE := hg _ (List.mem_map_of_mem List.mem_cons_self)
  rw [flat_eval 4 _ _ rfl] at hE
  convert hE using 1
  simp [Checker.Data.cornerK2y_goals, Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]
  unfold E1x j20; ring

theorem K3Fact_of_check (hc : Checker.check Checker.NP.centredEnc Checker.Data.cornerK3 = true) :
    K3Fact := by
  intro l t hl0 hl1 ht0 ht1 ht hx
  have hX : Checker.InBox [l, t] Checker.Data.cornerK3.box := by
    clear hc
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil) <;>
    · unfold Checker.Mem; simp only [Checker.Dy.cnum_toReal_mk]
      constructor <;> norm_num <;> linarith
  have hr2' : (1:ℝ) ^ 2 = Checker.NP.DPoly.eval Checker.Data.cornerK3.rSq [l, t] := by
    clear hc
    show (1:ℝ) ^ 2 = Checker.NP.DPoly.eval ⟨2, Checker.NP.ofFlat 2 Checker.Data.cornerK3_rSq⟩ _
    rw [flat_eval 2 _ _ rfl]
    simp [Checker.Data.cornerK3_rSq, Checker.evalR, Checker.monoR]
  have hhyp : ∀ p ∈ Checker.Data.cornerK3.hyps,
      0 ≤ Checker.NP.DPoly.eval p ([l, t] ++ [1]) := by
    clear hc
    intro p hp
    simp only [Checker.Data.cornerK3, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [flat_eval 3 q _ rfl]
    simp only [Checker.Data.cornerK3_hyps, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;>
    · simp [Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]; nlinarith
  have hg := Checker.check_sound Checker.NP.centredEnc_sound Checker.Data.cornerK3 hc _ hX 1
    one_pos hr2' hhyp
  have hE1 := hg _ (List.mem_map_of_mem List.mem_cons_self)
  have hE2 := hg _ (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [flat_eval 3 _ _ rfl] at hE1 hE2
  constructor
  · convert hE1 using 1
    simp [Checker.Data.cornerK3_goals, Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]
    unfold j20; ring
  · convert hE2 using 1
    simp [Checker.Data.cornerK3_goals, Checker.evalR, Checker.monoR, Checker.Dy.cnum_toReal_mk]
    unfold j20; ring

/-- The corner leaf, given the three kernel-checked certificates. -/
theorem corner_of_checks
    (h1 : Checker.check Checker.NP.centredEnc Checker.Data.cornerK1 = true)
    (h2 : Checker.check Checker.NP.centredEnc Checker.Data.cornerK2y = true)
    (h3 : Checker.check Checker.NP.centredEnc Checker.Data.cornerK3 = true) :
    K1Fact ∧ K2Fact :=
  ⟨K1Fact_of_check h1, K2Fact_of_K2x (K2xFact_of (K2yFact_of_check h2) (K3Fact_of_check h3))⟩

end BirkhoffGlobalSection.EHConvex.Corner

open BirkhoffGlobalSection.TangentialHessian in
theorem solution (c x₁ x₂ σ τ : ℝ) (hc : 2 ≤ c)
    (hb : 0 < Real.cos x₂)
    (h1 : |x₂| ≤ Real.pi / 2) (h0 : Real.cosh x₁ ^ 2 ≤ 2 * c)
    (hV : c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128 ≤ 0)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    let V := c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128
    let V₁ := c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
      Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32
    let V₂ := c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32
    let V₁₁ := c * Real.cosh (2 * x₁) / 2 - Real.cosh x₁ / 2 - Real.cosh (4 * x₁) / 16
    let V₂₂ := c * Real.cos (2 * x₂) / 2 - Real.cos (4 * x₂) / 16
    let r := Real.sqrt (-2 * V)
    let cc := V₁₁ + σ * r * |Real.sinh (2 * x₁)| / 2
    let dd := V₂₂ + τ * r * |Real.sin (2 * x₂)| / 2
    0 < r ^ 2 * cc * dd + cc * V₂ ^ 2 + dd * V₁ ^ 2 :=
  BirkhoffGlobalSection.EHConvex.Corner.corner_trig
    (BirkhoffGlobalSection.EHConvex.Corner.corner_of_checks Checker.Data.cornerK1_check
      Checker.Data.cornerK2y_check Checker.Data.cornerK3_check).1
    (BirkhoffGlobalSection.EHConvex.Corner.corner_of_checks Checker.Data.cornerK1_check
      Checker.Data.cornerK2y_check Checker.Data.cornerK3_check).2
    c x₁ x₂ σ τ hc hb h1 h0 hV hσ hτ
