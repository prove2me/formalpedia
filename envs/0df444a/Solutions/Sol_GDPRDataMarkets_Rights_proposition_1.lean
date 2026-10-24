-- Prove2me | solution 1 for GDPRDataMarkets.Rights.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T10:10:31.968654+00:00
-- url     : https://prove2.me/submissions/466a999e-bcfd-4689-a1cf-e314c37b5813

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

set_option autoImplicit false

noncomputable section

namespace GDPRP1

open MeasureTheory Set GDPRDataMarkets.Rights

/-! ### Part 1: the reduced first-period objective, as a function of the opt-in threshold -/

def V (w : ℝ) : ℝ := if w ^ 2 ≤ 1 / 2 then (1 - w ^ 2) / 2 else 1 / 4

def psi (k d x c w : ℝ) : ℝ :=
  ((1 + x) * w - c) * (1 - w) + d * (k * ((1 - w ^ 2) / 2) - c * (1 - w) + V w)

def psi1 (k d x c w : ℝ) : ℝ :=
  ((1 + x) * w - c) * (1 - w) + d * (k * ((1 - w ^ 2) / 2) - c * (1 - w) + (1 - w ^ 2) / 2)

def psi2 (k d x c w : ℝ) : ℝ :=
  ((1 + x) * w - c) * (1 - w) + d * (k * ((1 - w ^ 2) / 2) - c * (1 - w) + 1 / 4)

lemma psi_of_le {k d x c w : ℝ} (h : w ^ 2 ≤ 1 / 2) : psi k d x c w = psi1 k d x c w := by
  simp only [psi, psi1, V, if_pos h]

lemma psi_of_gt {k d x c w : ℝ} (h : ¬ w ^ 2 ≤ 1 / 2) : psi k d x c w = psi2 k d x c w := by
  simp only [psi, psi2, V, if_neg h]

lemma psi1_sub (k d x c u w : ℝ) :
    psi1 k d x c u - psi1 k d x c w
      = (w - u) * ((2 + d + d * k + 2 * x) * (w + u) / 2 - (1 + x + (1 + d) * c)) := by
  unfold psi1; ring

lemma psi2_sub (k d x c u w : ℝ) :
    psi2 k d x c u - psi2 k d x c w
      = (w - u) * ((2 + d * k + 2 * x) * (w + u) / 2 - (1 + x + (1 + d) * c)) := by
  unfold psi2; ring

def w0 : ℝ := Real.sqrt 2 / 2

lemma w0_sq : w0 ^ 2 = 1 / 2 := by
  unfold w0; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma w0_gt : (7 : ℝ) / 10 < w0 := by
  unfold w0
  have : (7 : ℝ) / 5 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

lemma psi2_w0 (k d x c : ℝ) : psi2 k d x c w0 = psi1 k d x c w0 := by
  unfold psi1 psi2; rw [w0_sq]; ring

lemma psi1_le_of {k d x c u w : ℝ} (huw : u ≤ w) (hD : 0 ≤ 2 + d + d * k + 2 * x)
    (hB : 1 + x + (1 + d) * c ≤ (2 + d + d * k + 2 * x) * u) :
    psi1 k d x c w ≤ psi1 k d x c u := by
  have he : 0 ≤ (2 + d + d * k + 2 * x) * (w + u) / 2 - (1 + x + (1 + d) * c) := by
    nlinarith [mul_le_mul_of_nonneg_left huw hD]
  have := mul_nonneg (sub_nonneg.2 huw) he
  linarith [psi1_sub k d x c u w]

lemma psi2_le_of {k d x c u w : ℝ} (huw : u ≤ w) (hD : 0 ≤ 2 + d * k + 2 * x)
    (hB : 1 + x + (1 + d) * c ≤ (2 + d * k + 2 * x) * u) :
    psi2 k d x c w ≤ psi2 k d x c u := by
  have he : 0 ≤ (2 + d * k + 2 * x) * (w + u) / 2 - (1 + x + (1 + d) * c) := by
    nlinarith [mul_le_mul_of_nonneg_left huw hD]
  have := mul_nonneg (sub_nonneg.2 huw) he
  linarith [psi2_sub k d x c u w]

/-- past `7/10` the `V = 1/4` branch is decreasing -/
lemma psi2_anti {k d x c u w : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hx : 0 < x)
    (hdk : (2 + d) * x ≤ d * k) (hc : c ≤ x) (hu : 7 / 10 ≤ u) (huw : u ≤ w) :
    psi2 k d x c w ≤ psi2 k d x c u := by
  have hD : 0 ≤ 2 + d * k + 2 * x := by nlinarith
  apply psi2_le_of huw hD
  have h1 := mul_le_mul_of_nonneg_left hu hD
  have h2 := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 1 + d)
  have h3 : d * x ≤ 1 * x := mul_le_mul_of_nonneg_right hd1 hx.le
  nlinarith

lemma core_A {k d x c t D : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hx : 0 < x)
    (hdk : (2 + d) * x ≤ d * k) (hct : c = x * t) (ht0 : 0 ≤ t) (htA : t ≤ 1 / 2)
    (hD : D = 2 + d + d * k + 2 * x) {w : ℝ} (hw : t ≤ w) (hw1 : w ≤ 1) :
    psi k d x c w ≤ psi k d x c (max ((1 + x + (1 + d) * c) / D) t) ∧
      (max ((1 + x + (1 + d) * c) / D) t) ^ 2 ≤ 1 / 2 ∧
      t ≤ max ((1 + x + (1 + d) * c) / D) t ∧ max ((1 + x + (1 + d) * c) / D) t ≤ 1 := by
  have hD0 : 0 < D := by rw [hD]; nlinarith
  set Y := (1 + x + (1 + d) * c) / D with hYdef
  have hB : 1 + x + (1 + d) * c = D * Y := by
    rw [hYdef, mul_div_assoc', mul_div_cancel_left₀ _ hD0.ne']
  have hc0 : 0 ≤ c := by rw [hct]; positivity
  have hcx : c ≤ x / 2 := by rw [hct]; nlinarith
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hY23 : Y ≤ 2 / 3 := by
    rw [hYdef, div_le_iff₀ hD0, hD]
    nlinarith [mul_le_mul_of_nonneg_left hcx (by linarith : (0 : ℝ) ≤ 1 + d)]
  have hvs : (max Y t) ^ 2 ≤ 1 / 2 := by
    rcases le_total Y t with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hv1 : max Y t ≤ 1 := max_le (by linarith) (by linarith)
  -- psi1 is maximised over [t, ∞) at max Y t
  have key : ∀ z, t ≤ z → psi1 k d x c z ≤ psi1 k d x c (max Y t) := by
    intro z hz
    rcases le_total t Y with h | h
    · rw [max_eq_left h]
      have e := psi1_sub k d x c Y z
      rw [← hD, hB] at e
      nlinarith [mul_nonneg hD0.le (sq_nonneg (z - Y))]
    · rw [max_eq_right h]
      apply psi1_le_of hz (by rw [← hD]; exact hD0.le)
      rw [← hD, hB]; exact mul_le_mul_of_nonneg_left h hD0.le
  refine ⟨?_, hvs, le_max_right _ _, hv1⟩
  rw [psi_of_le hvs]
  by_cases hw2 : w ^ 2 ≤ 1 / 2
  · rw [psi_of_le hw2]; exact key w hw
  · rw [psi_of_gt hw2]
    have hw0 := w0_gt
    have hww : w0 ≤ w := by nlinarith [w0_sq]
    calc psi2 k d x c w ≤ psi2 k d x c w0 :=
          psi2_anti hd0 hd1 hx hdk (by linarith) hw0.le hww
      _ = psi1 k d x c w0 := psi2_w0 k d x c
      _ ≤ psi1 k d x c (max Y t) := key w0 (by linarith)

lemma core_BC {k d x c t : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hx : 0 < x)
    (hdk : (2 + d) * x ≤ d * k) (hct : c = x * t) (ht : 1 / 2 < t) (ht1 : t < 1)
    {w : ℝ} (hw : t ≤ w) (hw1 : w ≤ 1) :
    psi k d x c w ≤ psi k d x c t := by
  have hD : 0 ≤ 2 + d + d * k + 2 * x := by nlinarith
  have hB : 1 + x + (1 + d) * c ≤ (2 + d + d * k + 2 * x) * t := by
    rw [hct]
    nlinarith [mul_le_mul_of_nonneg_right hdk (by linarith : (0 : ℝ) ≤ t),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - d) hx.le) (by linarith : (0 : ℝ) ≤ t),
      mul_nonneg hx.le (by linarith : (0 : ℝ) ≤ 3 * t - 1), mul_pos hd0 (by linarith : (0 : ℝ) < t)]
  have hcx : c ≤ x := by rw [hct]; nlinarith
  by_cases ht2 : t ^ 2 ≤ 1 / 2
  · rw [psi_of_le ht2]
    by_cases hw2 : w ^ 2 ≤ 1 / 2
    · rw [psi_of_le hw2]; exact psi1_le_of hw hD hB
    · rw [psi_of_gt hw2]
      have hw0 := w0_gt
      have hww : w0 ≤ w := by nlinarith [w0_sq]
      have htw0 : t ≤ w0 := by nlinarith [w0_sq]
      calc psi2 k d x c w ≤ psi2 k d x c w0 :=
            psi2_anti hd0 hd1 hx hdk hcx hw0.le hww
        _ = psi1 k d x c w0 := psi2_w0 k d x c
        _ ≤ psi1 k d x c t := psi1_le_of htw0 hD hB
  · rw [psi_of_gt ht2]
    have ht7 : 7 / 10 ≤ t := by nlinarith
    have hw2 : ¬ w ^ 2 ≤ 1 / 2 := by intro h; apply ht2; nlinarith
    rw [psi_of_gt hw2]
    exact psi2_anti hd0 hd1 hx hdk hcx ht7 hw

/-! ### Part 2: the model -/

section model

variable (P : Params)

/-- the personalized price at which the low type is just indifferent -/
def rL (v q : ℝ) : ℝ := (1 + P.kL) * v - P.c - max (v - q) 0

def rH (v q : ℝ) : ℝ := (1 + P.kH) * v - P.c - max (v - q) 0

def rr (v q : ℝ) : ℝ :=
  if R P v q (rH P v q) ≤ R P v q (rL P v q) ∧ R P v q (rH P v q + 1) ≤ R P v q (rL P v q) then
    rL P v q
  else if R P v q (rH P v q + 1) ≤ R P v q (rH P v q) then rH P v q else rH P v q + 1

lemma rev_eq (v κ q ρ : ℝ) :
    rev2opt P v κ q ρ =
      if ρ ≤ (1 + κ) * v - P.c - max (v - q) 0 then ρ else (if q ≤ v then q else 0) := by
  unfold rev2opt
  by_cases h : ρ ≤ (1 + κ) * v - P.c - max (v - q) 0
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]

lemma R_eq (v q ρ : ℝ) :
    R P v q ρ =
      ((if ρ ≤ rL P v q then ρ else (if q ≤ v then q else 0)) +
        (if ρ ≤ rH P v q then ρ else (if q ≤ v then q else 0))) / 2 := by
  unfold R; rw [rev_eq, rev_eq]; rfl

lemma abs3 (a b f ρ : ℝ) (hab : a ≤ b) :
    ((if ρ ≤ a then ρ else f) + (if ρ ≤ b then ρ else f)) / 2 ≤
        ((if a ≤ a then a else f) + (if a ≤ b then a else f)) / 2 ∨
      ((if ρ ≤ a then ρ else f) + (if ρ ≤ b then ρ else f)) / 2 ≤
        ((if b ≤ a then b else f) + (if b ≤ b then b else f)) / 2 ∨
      ((if ρ ≤ a then ρ else f) + (if ρ ≤ b then ρ else f)) / 2 ≤
        ((if b + 1 ≤ a then b + 1 else f) + (if b + 1 ≤ b then b + 1 else f)) / 2 := by
  by_cases h1 : ρ ≤ a
  · left; rw [if_pos h1, if_pos (h1.trans hab), if_pos le_rfl, if_pos hab]; linarith
  · by_cases h2 : ρ ≤ b
    · right; left
      rw [if_neg h1, if_pos h2, if_pos le_rfl]
      by_cases h3 : b ≤ a
      · exact absurd (h2.trans h3) h1
      · rw [if_neg h3]; linarith
    · right; right
      rw [if_neg h1, if_neg h2, if_neg (by linarith), if_neg (by linarith)]

lemma rL_le_rH (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q : ℝ) : rL P v q ≤ rH P v q := by
  unfold rL rH; have := hS.2.1; nlinarith

lemma R_opt (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q ρ : ℝ) : R P v q ρ ≤ R P v q (rr P v q) := by
  have hab := rL_le_rH P hS hv q
  have key : R P v q ρ ≤ R P v q (rL P v q) ∨ R P v q ρ ≤ R P v q (rH P v q) ∨
      R P v q ρ ≤ R P v q (rH P v q + 1) := by
    rw [R_eq P v q ρ, R_eq P v q (rL P v q), R_eq P v q (rH P v q), R_eq P v q (rH P v q + 1)]
    exact abs3 _ _ _ ρ hab
  unfold rr
  split_ifs with h1 h2
  · rcases key with k | k | k <;> linarith [h1.1, h1.2]
  · have : R P v q (rL P v q) ≤ R P v q (rH P v q) := by
      by_contra hc; push Not at hc
      exact h1 ⟨hc.le, by linarith⟩
    rcases key with k | k | k <;> linarith
  · have : R P v q (rL P v q) ≤ R P v q (rH P v q + 1) := by
      by_contra hc; push Not at hc
      exact h1 ⟨by linarith, hc.le⟩
    rcases key with k | k | k <;> linarith

lemma rr_ge (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q : ℝ) : rL P v q ≤ rr P v q := by
  have := rL_le_rH P hS hv q
  unfold rr; split_ifs <;> linarith

lemma R_rL (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q : ℝ) : R P v q (rL P v q) = rL P v q := by
  rw [R_eq, if_pos le_rfl, if_pos (rL_le_rH P hS hv q)]; ring

lemma rr_eq (hS : P.Standing) (hA : P.Assumption1) {v : ℝ} (hv : 0 ≤ v) (q : ℝ)
    (hc : P.c ≤ P.d * P.sigma * v) : rr P v q = rL P v q := by
  have hab := rL_le_rH P hS hv q
  have hA' : P.d * P.sigma ≤ 2 * P.kL - P.kH := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hk := mul_le_mul_of_nonneg_right hA' hv
  have hf : (if q ≤ v then q else 0) + (rH P v q - rL P v q) ≤ rL P v q := by
    unfold rL rH
    split_ifs with hq
    · rw [max_eq_left (by linarith : 0 ≤ v - q)]; nlinarith
    · rw [max_eq_right (by linarith : v - q ≤ 0)]; nlinarith
  unfold rr
  rw [if_pos]
  constructor
  · rw [R_eq P v q (rH P v q), R_rL P hS hv, if_pos le_rfl]
    generalize (if q ≤ v then q else 0) = f at hf ⊢
    split_ifs with h1 <;> linarith
  · rw [R_eq P v q (rH P v q + 1), R_rL P hS hv,
      if_neg (show ¬ (rH P v q + 1 ≤ rL P v q) by linarith),
      if_neg (show ¬ (rH P v q + 1 ≤ rH P v q) by linarith)]
    generalize (if q ≤ v then q else 0) = f at hf ⊢
    linarith

lemma u2_le (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q : ℝ) :
    (u2opt P v P.kL q (rr P v q) + u2opt P v P.kH q (rr P v q)) / 2 ≤
      max (v - q) 0 + P.sigma * v := by
  have hge := rr_ge P hS hv q
  unfold rL at hge
  have hk := hS.2.1
  have h1 : u2opt P v P.kL q (rr P v q) = max (v - q) 0 := by
    unfold u2opt; exact max_eq_right (by linarith)
  have h2 : u2opt P v P.kH q (rr P v q) ≤ max (v - q) 0 + (P.kH - P.kL) * v := by
    unfold u2opt
    exact max_le (by linarith) (by nlinarith)
  rw [h1]; unfold Params.sigma; linarith

lemma u2_eq (hS : P.Standing) (hA : P.Assumption1) {v : ℝ} (hv : 0 ≤ v) (q : ℝ)
    (hc : P.c ≤ P.d * P.sigma * v) :
    (u2opt P v P.kL q (rr P v q) + u2opt P v P.kH q (rr P v q)) / 2 =
      max (v - q) 0 + P.sigma * v := by
  rw [rr_eq P hS hA hv q hc]
  have hk := hS.2.1
  have h1 : u2opt P v P.kL q (rL P v q) = max (v - q) 0 := by
    unfold u2opt rL; exact max_eq_right (by linarith)
  have h2 : u2opt P v P.kH q (rL P v q) = max (v - q) 0 + (P.kH - P.kL) * v := by
    unfold u2opt rL
    rw [max_eq_left (by nlinarith)]; ring
  rw [h1, h2]; unfold Params.sigma; ring

def q2 (w : ℝ) : ℝ := if w ^ 2 ≤ 1 / 2 then 1 else 1 / 2

/-- the candidate profile: opt in above the threshold `W p₁`, buy without opting in above `p₁` -/
def prof (W : ℝ → ℝ) (p : ℝ) : Profile where
  p1 := p
  p2 := fun p1 => q2 (min 1 (W p1))
  r := rr P
  choice := fun p1 v => if W p1 ≤ v then .optIn else if p1 ≤ v then .buy else .none

lemma cons_opt (hS : P.Standing) (hA : P.Assumption1) (W : ℝ → ℝ) (p : ℝ)
    (hW : ∀ p1, ∀ v ∈ Icc (0 : ℝ) 1,
      (W p1 ≤ v → P.c ≤ P.d * P.sigma * v ∧ p1 ≤ (1 + P.d * P.sigma) * v - P.c) ∧
      (v < W p1 → P.d * P.sigma * v ≤ P.c ∨ (1 + P.d * P.sigma) * v - P.c < p1)) :
    ∀ p1 : ℝ, ∀ v ∈ Icc (0 : ℝ) 1, ∀ a : FirstChoice,
      U1 P (prof P W p) p1 v a ≤ U1 P (prof P W p) p1 v ((prof P W p).choice p1 v) := by
  intro p1 v hv a
  obtain ⟨h1, h2⟩ := hW p1 v hv
  have hd : 0 < P.d := hS.2.2.1
  have hr : (prof P W p).r = rr P := rfl
  have hle := mul_le_mul_of_nonneg_left (u2_le P hS hv.1 ((prof P W p).p2 p1)) hd.le
  have hch : (prof P W p).choice p1 v =
      if W p1 ≤ v then .optIn else if p1 ≤ v then .buy else .none := rfl
  rw [hch]
  split_ifs with hw hp
  · obtain ⟨hc, hp1⟩ := h1 hw
    have heq := u2_eq P hS hA hv.1 ((prof P W p).p2 p1) hc
    cases a <;> simp only [U1, hr, heq] <;> nlinarith
  · have h2' := h2 (lt_of_not_ge hw)
    cases a <;> simp only [U1, hr] at hle ⊢ <;> rcases h2' with h | h <;> nlinarith
  · have h2' := h2 (lt_of_not_ge hw)
    have hp' : v < p1 := lt_of_not_ge hp
    cases a <;> simp only [U1, hr] at hle ⊢ <;> rcases h2' with h | h <;> nlinarith

lemma vol_sandwich {s : Set ℝ} {a b : ℝ} (h1 : Ioo a b ⊆ s) (h2 : s ⊆ Icc a b) :
    (volume s).toReal = max (b - a) 0 := by
  have : volume s = ENNReal.ofReal (b - a) :=
    le_antisymm (by rw [← Real.volume_Icc]; exact measure_mono h2)
      (by rw [← Real.volume_Ioo]; exact measure_mono h1)
  rw [this, ENNReal.toReal_ofReal']

lemma choice_optIn (W : ℝ → ℝ) (p p1 v : ℝ) :
    (prof P W p).choice p1 v = .optIn ↔ W p1 ≤ v := by
  show (if W p1 ≤ v then FirstChoice.optIn else if p1 ≤ v then FirstChoice.buy
    else FirstChoice.none) = .optIn ↔ _
  split_ifs with h1 h2 <;> simp [h1]

lemma choice_none (W : ℝ → ℝ) (p p1 v : ℝ) :
    (prof P W p).choice p1 v = .none ↔ v < W p1 ∧ v < p1 := by
  show (if W p1 ≤ v then FirstChoice.optIn else if p1 ≤ v then FirstChoice.buy
    else FirstChoice.none) = .none ↔ _
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp only [true_iff]; exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩

lemma buyer_vol (W : ℝ → ℝ) (p p1 : ℝ) :
    (volume (buyerSet (prof P W p) p1)).toReal = max (1 - max 0 (min (W p1) p1)) 0 := by
  apply vol_sandwich
  · intro v hv
    simp only [mem_Ioo, max_lt_iff, min_lt_iff] at hv
    simp only [buyerSet, mem_setOf_eq, mem_Icc, ne_eq, choice_none, not_and, not_lt]
    refine ⟨⟨hv.1.1.le, hv.2.le⟩, fun h => ?_⟩
    rcases hv.1.2 with h' | h'
    · exact absurd h (not_lt.2 h'.le)
    · exact h'.le
  · intro v hv
    simp only [buyerSet, mem_setOf_eq, mem_Icc, ne_eq, choice_none, not_and, not_lt] at hv
    simp only [mem_Icc, max_le_iff, min_le_iff]
    refine ⟨⟨hv.1.1, ?_⟩, hv.1.2⟩
    by_cases h : W p1 ≤ v
    · exact Or.inl h
    · exact Or.inr (hv.2 (lt_of_not_ge h))

lemma rL_cont (q : ℝ) : Continuous (fun v => rL P v q) := by
  unfold rL; fun_prop

lemma integ_lin (A B w : ℝ) : ∫ v in w..1, (A * v + B) = A * ((1 - w ^ 2) / 2) + B * (1 - w) := by
  rw [intervalIntegral.integral_add (f := fun v => A * v) (g := fun _ => B)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma int_q1 {w : ℝ} (hw1 : w ≤ 1) :
    ∫ v in w..1, rL P v 1 = (1 + P.kL) * ((1 - w ^ 2) / 2) + (-P.c) * (1 - w) := by
  rw [← integ_lin]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hw1] at hv
  simp only [rL]
  rw [max_eq_right (by linarith [hv.2])]; ring

lemma int_qh {w : ℝ} (hw : 1 / 2 ≤ w) (hw1 : w ≤ 1) :
    ∫ v in w..1, rL P v (1 / 2) = P.kL * ((1 - w ^ 2) / 2) + (1 / 2 - P.c) * (1 - w) := by
  rw [← integ_lin]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hw1] at hv
  simp only [rL]
  rw [max_eq_left (by linarith [hv.1])]; ring

lemma int_up1 {w : ℝ} (hw1 : w ≤ 1) (q : ℝ) :
    ∫ v in w..1, rL P v q ≤ (1 + P.kL) * ((1 - w ^ 2) / 2) + (-P.c) * (1 - w) := by
  rw [← integ_lin]
  refine intervalIntegral.integral_mono_on hw1 ((rL_cont P q).intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop) ?_
  intro v _
  simp only [rL]; linarith [le_max_right (v - q) 0]

lemma int_up2 {w : ℝ} (hw1 : w ≤ 1) (q : ℝ) :
    ∫ v in w..1, rL P v q ≤ P.kL * ((1 - w ^ 2) / 2) + (q - P.c) * (1 - w) := by
  rw [← integ_lin]
  refine intervalIntegral.integral_mono_on hw1 ((rL_cont P q).intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop) ?_
  intro v _
  simp only [rL]; linarith [le_max_left (v - q) 0]

def Gv (w : ℝ) : ℝ := P.kL * ((1 - w ^ 2) / 2) - P.c * (1 - w) + V w

lemma cont_val {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (∫ v in w..1, rL P v (q2 w)) + q2 w * max (w - max (q2 w) 0) 0 = Gv P w := by
  unfold q2 Gv V
  split_ifs with h
  · rw [int_q1 P hw1, max_eq_left (zero_le_one), max_eq_right (by linarith : w - 1 ≤ 0)]; ring
  · have hw2 : 1 / 2 ≤ w := by
      by_contra hc; push Not at hc; apply h; nlinarith
    rw [int_qh P hw2 hw1, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
      max_eq_left (by linarith : 0 ≤ w - 1 / 2)]
    ring

lemma cont_le {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (q : ℝ) :
    (∫ v in w..1, rL P v q) + q * max (w - max q 0) 0 ≤ Gv P w := by
  have u1 := int_up1 P hw1 q
  have u2 := int_up2 P hw1 q
  have hV1 : (1 - w ^ 2) / 2 ≤ V w := by unfold V; split_ifs <;> nlinarith
  have hV2 : 1 / 4 ≤ V w := by unfold V; split_ifs <;> nlinarith
  unfold Gv
  rcases le_or_gt q 0 with hq | hq
  · rw [max_eq_right hq, sub_zero, max_eq_left hw0]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hq hw0]
  · rw [max_eq_left hq.le]
    rcases le_or_gt q w with hqw | hqw
    · rw [max_eq_left (by linarith : 0 ≤ w - q)]
      nlinarith [sq_nonneg (q - 1 / 2)]
    · rw [max_eq_right (by linarith : w - q ≤ 0), mul_zero, add_zero]
      linarith

lemma profit2_eq (hS : P.Standing) (hA : P.Assumption1) (W : ℝ → ℝ) (p p1 q : ℝ)
    (hW0 : 0 ≤ W p1) (hW1 : ∀ v ∈ Icc (0 : ℝ) 1, W p1 ≤ v → P.c ≤ P.d * P.sigma * v) :
    profit2 P (prof P W p) p1 q =
      (∫ v in (min 1 (W p1))..1, rL P v q) + q * max (min 1 (W p1) - max q 0) 0 := by
  unfold profit2
  congr 1
  · have hset : optInSet (prof P W p) p1 = Icc 0 1 ∩ Ici (W p1) := by
      ext v; simp only [optInSet, mem_setOf_eq, choice_optIn, mem_inter_iff, mem_Ici]
    have hcongr : ∫ v in Icc 0 1 ∩ Ici (W p1), R P v q ((prof P W p).r v q) =
        ∫ v in Icc 0 1 ∩ Ici (W p1), rL P v q :=
      setIntegral_congr_fun (measurableSet_Icc.inter measurableSet_Ici) (fun v hv => by
        show R P v q (rr P v q) = rL P v q
        rw [rr_eq P hS hA hv.1.1 q (hW1 v hv.1 hv.2), R_rL P hS hv.1.1])
    rw [hset, hcongr]
    by_cases h : W p1 ≤ 1
    · have : Icc (0 : ℝ) 1 ∩ Ici (W p1) = Icc (W p1) 1 := by
        ext v; simp only [mem_inter_iff, mem_Icc, mem_Ici]; constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h2, h3⟩; exact ⟨⟨hW0.trans h2, h3⟩, h2⟩
      rw [this, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h, min_eq_right h]
    · have : Icc (0 : ℝ) 1 ∩ Ici (W p1) = ∅ := by
        ext v; simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h2⟩, h3⟩; exact h (h3.trans h2)
      rw [this, setIntegral_empty, min_eq_left (le_of_lt (not_le.1 h)),
        intervalIntegral.integral_same]
  · congr 1
    apply vol_sandwich
    · intro v hv
      simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hv
      simp only [mem_setOf_eq, mem_Icc, ne_eq, choice_optIn, not_le]
      exact ⟨⟨hv.1.2.le, hv.2.1.le⟩, hv.2.2, hv.1.1.le⟩
    · intro v hv
      simp only [mem_setOf_eq, mem_Icc, ne_eq, choice_optIn, not_le] at hv
      simp only [mem_Icc, max_le_iff, le_min_iff]
      exact ⟨⟨hv.2.2, hv.1.1⟩, hv.1.2, hv.2.1.le⟩

def Phi (W : ℝ → ℝ) (p1 : ℝ) : ℝ :=
  p1 * max (1 - max 0 (min (W p1) p1)) 0 + P.d * Gv P (min 1 (W p1))

lemma profit_eq (hS : P.Standing) (hA : P.Assumption1) (W : ℝ → ℝ) (p p1 : ℝ)
    (hW0 : 0 ≤ W p1) (hW1 : ∀ v ∈ Icc (0 : ℝ) 1, W p1 ≤ v → P.c ≤ P.d * P.sigma * v) :
    profit P (prof P W p) p1 = Phi P W p1 := by
  unfold profit Phi
  have hp2 : (prof P W p).p2 p1 = q2 (min 1 (W p1)) := rfl
  rw [buyer_vol, hp2, profit2_eq P hS hA W p p1 _ hW0 hW1,
    cont_val P (le_min zero_le_one hW0) (min_le_left _ _)]

lemma equil (hS : P.Standing) (hA : P.Assumption1) (W : ℝ → ℝ) (p : ℝ)
    (hW0 : ∀ p1, 0 ≤ W p1)
    (hW : ∀ p1, ∀ v ∈ Icc (0 : ℝ) 1,
      (W p1 ≤ v → P.c ≤ P.d * P.sigma * v ∧ p1 ≤ (1 + P.d * P.sigma) * v - P.c) ∧
      (v < W p1 → P.d * P.sigma * v ≤ P.c ∨ (1 + P.d * P.sigma) * v - P.c < p1))
    (hmax : ∀ p1, Phi P W p1 ≤ Phi P W p) : IsEquilibrium P (prof P W p) := by
  have hW1 : ∀ p1, ∀ v ∈ Icc (0 : ℝ) 1, W p1 ≤ v → P.c ≤ P.d * P.sigma * v :=
    fun p1 v hv h => ((hW p1 v hv).1 h).1
  refine ⟨fun v hv q ρ => R_opt P hS hv.1 q ρ, fun p1 q => ?_, cons_opt P hS hA W p hW,
    fun p1 => ?_⟩
  · have hp2 : (prof P W p).p2 p1 = q2 (min 1 (W p1)) := rfl
    rw [hp2, profit2_eq P hS hA W p p1 q (hW0 p1) (hW1 p1),
      profit2_eq P hS hA W p p1 _ (hW0 p1) (hW1 p1),
      cont_val P (le_min zero_le_one (hW0 p1)) (min_le_left _ _)]
    exact cont_le P (le_min zero_le_one (hW0 p1)) (min_le_left _ _) q
  · show profit P (prof P W p) p1 ≤ profit P (prof P W p) p
    rw [profit_eq P hS hA W p p1 (hW0 p1) (hW1 p1), profit_eq P hS hA W p p (hW0 p) (hW1 p)]
    exact hmax p1

lemma keeps_L (v q : ℝ) : keeps P v P.kL q (rL P v q) := by
  unfold keeps rL; linarith

lemma keeps_H (hS : P.Standing) {v : ℝ} (hv : 0 ≤ v) (q : ℝ) : keeps P v P.kH q (rL P v q) := by
  unfold keeps rL; have := hS.2.1; nlinarith

lemma rL_one {v : ℝ} (hv : v ≤ 1) : rL P v 1 = (1 + P.mu - P.sigma) * v - P.c := by
  unfold rL Params.mu Params.sigma; rw [max_eq_right (by linarith)]; ring

lemma rL_half {v : ℝ} (hv : 1 / 2 ≤ v) : rL P v (1 / 2) = (P.mu - P.sigma) * v + 1 / 2 - P.c := by
  unfold rL Params.mu Params.sigma; rw [max_eq_left (by linarith)]; ring

/-! ### Part 3: the threshold `vStar` -/

lemma vStar_conds (hx : 0 < P.d * P.sigma) :
    ∀ p1, ∀ v ∈ Icc (0 : ℝ) 1,
      (vStar P p1 ≤ v → P.c ≤ P.d * P.sigma * v ∧ p1 ≤ (1 + P.d * P.sigma) * v - P.c) ∧
      (v < vStar P p1 → P.d * P.sigma * v ≤ P.c ∨ (1 + P.d * P.sigma) * v - P.c < p1) := by
  intro p1 v _
  have h1x : 0 < 1 + P.d * P.sigma := by linarith
  unfold vStar
  constructor
  · intro h
    have h1 := (le_max_left _ _).trans h
    have h2 := (le_max_right _ _).trans h
    rw [div_le_iff₀ hx] at h1
    rw [div_le_iff₀ h1x] at h2
    constructor <;> nlinarith
  · intro h
    rcases lt_max_iff.1 h with h1 | h1
    · left; rw [lt_div_iff₀ hx] at h1; nlinarith
    · right; rw [lt_div_iff₀ h1x] at h1; nlinarith

lemma vStar_nonneg (hS : P.Standing) (hx : 0 < P.d * P.sigma) (p1 : ℝ) : 0 ≤ vStar P p1 :=
  le_max_of_le_left (div_nonneg hS.2.2.2.2 hx.le)

lemma Phi_le_t (hx : 0 < P.d * P.sigma) {t : ℝ} (hct : P.c = P.d * P.sigma * t) (ht1 : t < 1)
    {p1 : ℝ} (h : p1 ≤ t) :
    Phi P (vStar P) p1 = p1 * max (1 - max 0 p1) 0 + P.d * Gv P t := by
  have htc : P.c / (P.d * P.sigma) = t := by rw [hct]; exact mul_div_cancel_left₀ t hx.ne'
  have ha : (p1 + P.c) / (1 + P.d * P.sigma) ≤ t := by
    rw [div_le_iff₀ (by linarith), hct]; nlinarith
  unfold Phi vStar
  rw [htc, max_eq_left ha, min_eq_right h, min_eq_right ht1.le]

lemma Phi_gt_t (hS : P.Standing) (hx : 0 < P.d * P.sigma) {t : ℝ} (hct : P.c = P.d * P.sigma * t)
    (ht1 : t < 1) {p1 : ℝ} (h : t < p1) :
    ∃ w, t ≤ w ∧ w ≤ 1 ∧ Phi P (vStar P) p1 = psi P.kL P.d (P.d * P.sigma) P.c w := by
  have ht0 : 0 ≤ t := by
    have := hS.2.2.2.2; rw [hct] at this
    by_contra hc; push Not at hc; nlinarith
  have htc : P.c / (P.d * P.sigma) = t := by rw [hct]; exact mul_div_cancel_left₀ t hx.ne'
  have h1x : 0 < 1 + P.d * P.sigma := by linarith
  have hta : t ≤ (p1 + P.c) / (1 + P.d * P.sigma) := by
    rw [le_div_iff₀ h1x, hct]; nlinarith
  have hap : (p1 + P.c) / (1 + P.d * P.sigma) ≤ p1 := by
    rw [div_le_iff₀ h1x, hct]; nlinarith [mul_le_mul_of_nonneg_left h.le hx.le]
  unfold Phi vStar
  rw [htc, max_eq_right hta, min_eq_left hap, max_eq_right (ht0.trans hta)]
  refine ⟨min 1 ((p1 + P.c) / (1 + P.d * P.sigma)), le_min ht1.le hta, min_le_left _ _, ?_⟩
  rcases le_total ((p1 + P.c) / (1 + P.d * P.sigma)) 1 with ha1 | ha1
  · rw [min_eq_right ha1, max_eq_left (by linarith)]
    have hp : (1 + P.d * P.sigma) * ((p1 + P.c) / (1 + P.d * P.sigma)) - P.c = p1 := by
      field_simp; ring
    simp only [psi, Gv]; rw [hp]
  · rw [min_eq_left ha1, max_eq_right (by linarith)]
    simp only [psi, Gv]; ring

lemma psi_t {t : ℝ} (hct : P.c = P.d * P.sigma * t) :
    psi P.kL P.d (P.d * P.sigma) P.c t = t * (1 - t) + P.d * Gv P t := by
  simp only [psi, Gv]; rw [hct]; ring

end model

lemma regBC_max (P : Params) (hS : P.Standing) (hA : P.Assumption1)
    (ht12 : 1 / 2 < P.c / (P.d * P.sigma)) (ht1 : P.c / (P.d * P.sigma) < 1) :
    ∀ p1, Phi P (vStar P) p1 ≤ Phi P (vStar P) (1 / 2) := by
  have hd0 : 0 < P.d := hS.2.2.1
  have hd1 : P.d ≤ 1 := hS.2.2.2.1
  have hc0 : 0 ≤ P.c := hS.2.2.2.2
  have hsig : 0 < P.sigma := by unfold Params.sigma; linarith [hS.2.1]
  have hx : 0 < P.d * P.sigma := mul_pos hd0 hsig
  have hk : (2 + P.d) * P.sigma ≤ P.kL := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hdk : (2 + P.d) * (P.d * P.sigma) ≤ P.d * P.kL := by
    nlinarith [mul_le_mul_of_nonneg_left hk hd0.le]
  set t := P.c / (P.d * P.sigma) with htdef
  have hct : P.c = P.d * P.sigma * t := by
    rw [htdef, mul_div_assoc', mul_div_cancel_left₀ _ hx.ne']
  have ht0 : 0 ≤ t := div_nonneg hc0 hx.le
  have hD0 : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    have : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
      simp only [Params.mu, Params.sigma]; ring
    rw [this]; nlinarith
  have hD : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
    simp only [Params.mu, Params.sigma]; ring
  have hW := vStar_conds P hx
  have hW0 := vStar_nonneg P hS hx
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hBC : 1 / 2 < t → t < 1 →
      ∀ p1, Phi P (vStar P) p1 ≤ Phi P (vStar P) (1 / 2) := by
    intro ht12 ht1 p1
    rw [Phi_le_t P hx hct ht1 (by linarith : (1 : ℝ) / 2 ≤ t)]
    have e : (1 / 2 : ℝ) * max (1 - max 0 (1 / 2)) 0 = 1 / 4 := by norm_num
    rw [e]
    rcases le_or_gt p1 t with h | h
    · rw [Phi_le_t P hx hct ht1 h]
      have : p1 * max (1 - max 0 p1) 0 ≤ 1 / 4 := by
        rcases le_or_gt p1 0 with h0 | h0
        · rw [max_eq_left h0, sub_zero, max_eq_left zero_le_one]; linarith
        · rw [max_eq_right h0.le, max_eq_left (by linarith)]; nlinarith [sq_nonneg (p1 - 1 / 2)]
      linarith
    · obtain ⟨w, hw, hw1, he⟩ := Phi_gt_t P hS hx hct ht1 h
      rw [he]
      have h1 := core_BC hd0 hd1 hx hdk hct ht12 ht1 hw hw1
      rw [psi_t P hct] at h1
      nlinarith [sq_nonneg (t - 1 / 2)]
  exact hBC ht12 ht1


lemma regA (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.c ≤ P.d * P.sigma / 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = P1star P ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v1star P ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < v1star P →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) := by
  have hd0 : 0 < P.d := hS.2.2.1
  have hd1 : P.d ≤ 1 := hS.2.2.2.1
  have hc0 : 0 ≤ P.c := hS.2.2.2.2
  have hsig : 0 < P.sigma := by unfold Params.sigma; linarith [hS.2.1]
  have hx : 0 < P.d * P.sigma := mul_pos hd0 hsig
  have hk : (2 + P.d) * P.sigma ≤ P.kL := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hdk : (2 + P.d) * (P.d * P.sigma) ≤ P.d * P.kL := by
    nlinarith [mul_le_mul_of_nonneg_left hk hd0.le]
  set t := P.c / (P.d * P.sigma) with htdef
  have hct : P.c = P.d * P.sigma * t := by
    rw [htdef, mul_div_assoc', mul_div_cancel_left₀ _ hx.ne']
  have ht0 : 0 ≤ t := div_nonneg hc0 hx.le
  have hD0 : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    have : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
      simp only [Params.mu, Params.sigma]; ring
    rw [this]; nlinarith
  have hD : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
    simp only [Params.mu, Params.sigma]; ring
  have hW := vStar_conds P hx
  have hW0 := vStar_nonneg P hS hx
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  intro hcA
  have htA : t ≤ 1 / 2 := by rw [hct] at hcA; nlinarith
  have ht1 : t < 1 := by linarith
  have hcore := fun w (hw : t ≤ w) (hw1 : w ≤ 1) => core_A hd0 hd1 hx hdk hct ht0 htA hD hw hw1
  set Y := (1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma)
    with hY
  obtain ⟨-, hvs2, htv, hv1⟩ := hcore t le_rfl ht1.le
  set vs := max Y t with hvsdef
  have hD0' := hD0.ne'
  have hX : ((1 + P.d * P.sigma) ^ 2 - (1 + P.d * P.mu - P.d ^ 2 * P.sigma) * P.c) /
      (2 + P.d + P.d * P.mu + P.d * P.sigma) = (1 + P.d * P.sigma) * Y - P.c := by
    rw [hY]; field_simp; ring
  have hP1 : P1star P = (1 + P.d * P.sigma) * vs - P.c := by
    unfold P1star; rw [← htdef, hX, hvsdef]
    rcases le_total Y t with h | h
    · rw [max_eq_right h, max_eq_right (by rw [hct]; nlinarith [mul_le_mul_of_nonneg_left h hx.le])]
      rw [hct]; ring
    · rw [max_eq_left h, max_eq_left (by rw [hct]; nlinarith [mul_le_mul_of_nonneg_left h hx.le])]
  have hvsP : vStar P (P1star P) = vs := by
    unfold vStar; rw [← htdef, hP1]
    have : ((1 + P.d * P.sigma) * vs - P.c + P.c) / (1 + P.d * P.sigma) = vs := by
      rw [sub_add_cancel, mul_div_cancel_left₀ _ (by linarith)]
    rw [this, max_eq_right htv]
  have hvsle : vs ≤ P1star P := by
    rw [hP1, hct]; nlinarith [mul_le_mul_of_nonneg_left htv hx.le]
  have hPhiStar : Phi P (vStar P) (P1star P) = psi P.kL P.d (P.d * P.sigma) P.c vs := by
    unfold Phi
    rw [hvsP, min_eq_left hvsle, max_eq_right (ht0.trans htv), max_eq_left (by linarith),
      min_eq_right hv1, hP1]
    rfl
  have hmax : ∀ p1, Phi P (vStar P) p1 ≤ Phi P (vStar P) (P1star P) := by
    intro p1; rw [hPhiStar]
    rcases le_or_gt p1 t with h | h
    · rw [Phi_le_t P hx hct ht1 h]
      have h1 : p1 * max (1 - max 0 p1) 0 ≤ t * (1 - t) := by
        rcases le_or_gt p1 0 with h0 | h0
        · rw [max_eq_left h0, sub_zero, max_eq_left zero_le_one]; nlinarith
        · rw [max_eq_right h0.le, max_eq_left (by linarith)]; nlinarith
      have h2 := (hcore t le_rfl ht1.le).1
      rw [psi_t P hct] at h2; linarith
    · obtain ⟨w, hw, hw1, he⟩ := Phi_gt_t P hS hx hct ht1 h
      rw [he]; exact (hcore w hw hw1).1
  have hp2 : (prof P (vStar P) (P1star P)).p2 (prof P (vStar P) (P1star P)).p1 = 1 := by
    show q2 (min 1 (vStar P (P1star P))) = 1
    rw [hvsP, min_eq_right hv1]; unfold q2; rw [if_pos hvs2]
  refine ⟨prof P (vStar P) (P1star P), equil P hS hA _ _ hW0 hW hmax, rfl, hp2, ?_, ?_⟩
  · intro v hv hvv
    have hvv' : vs ≤ v := hvv
    have hcv : P.c ≤ P.d * P.sigma * v := by
      rw [hct]; nlinarith [mul_le_mul_of_nonneg_left (htv.trans hvv') hx.le]
    rw [hp2]
    refine ⟨(choice_optIn P _ _ _ _).2 (by show vStar P (P1star P) ≤ v; rw [hvsP]; exact hvv'),
      ?_, ?_, ?_⟩
    · show keeps P v P.kL 1 (rr P v 1)
      rw [rr_eq P hS hA hv.1 1 hcv]; exact keeps_L P v 1
    · show keeps P v P.kH 1 (rr P v 1)
      rw [rr_eq P hS hA hv.1 1 hcv]; exact keeps_H P hS hv.1 1
    · show rr P v 1 = _
      rw [rr_eq P hS hA hv.1 1 hcv]; exact rL_one P hv.2
  · intro v hv hvv
    have hvv' : v < vs := hvv
    rw [hp2]
    refine ⟨(choice_none P _ _ _ _).2 ⟨?_, ?_⟩, by linarith⟩
    · show v < vStar P (P1star P); rw [hvsP]; exact hvv'
    · show v < P1star P; linarith


lemma regB (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.d * P.sigma / 2 < P.c ∧ P.c ≤ P.d * P.sigma / Real.sqrt 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ v < s.p2 s.p1) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) := by
  have hd0 : 0 < P.d := hS.2.2.1
  have hd1 : P.d ≤ 1 := hS.2.2.2.1
  have hc0 : 0 ≤ P.c := hS.2.2.2.2
  have hsig : 0 < P.sigma := by unfold Params.sigma; linarith [hS.2.1]
  have hx : 0 < P.d * P.sigma := mul_pos hd0 hsig
  have hk : (2 + P.d) * P.sigma ≤ P.kL := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hdk : (2 + P.d) * (P.d * P.sigma) ≤ P.d * P.kL := by
    nlinarith [mul_le_mul_of_nonneg_left hk hd0.le]
  set t := P.c / (P.d * P.sigma) with htdef
  have hct : P.c = P.d * P.sigma * t := by
    rw [htdef, mul_div_assoc', mul_div_cancel_left₀ _ hx.ne']
  have ht0 : 0 ≤ t := div_nonneg hc0 hx.le
  have hD0 : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    have : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
      simp only [Params.mu, Params.sigma]; ring
    rw [this]; nlinarith
  have hD : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
    simp only [Params.mu, Params.sigma]; ring
  have hW := vStar_conds P hx
  have hW0 := vStar_nonneg P hS hx
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hvs12 : 1 / 2 ≤ t → vStar P (1 / 2) = t := by
    intro h
    unfold vStar; rw [← htdef]; apply max_eq_left
    rw [div_le_iff₀ (by linarith), hct]; nlinarith
  intro hcB
  obtain ⟨hcB1, hcB2⟩ := hcB
  have ht12 : 1 / 2 < t := by rw [hct] at hcB1; nlinarith
  rw [le_div_iff₀ hs2, hct] at hcB2
  have hts : t * Real.sqrt 2 ≤ 1 := by
    by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hx]
  have e : (t * Real.sqrt 2) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs2sq]; ring
  have hsq : t ^ 2 ≤ 1 / 2 := by nlinarith [mul_nonneg ht0 hs2.le]
  have ht1 : t < 1 := by nlinarith
  have hp2 : (prof P (vStar P) (1 / 2)).p2 (prof P (vStar P) (1 / 2)).p1 = 1 := by
    show q2 (min 1 (vStar P (1 / 2))) = 1
    rw [hvs12 ht12.le, min_eq_right ht1.le]; unfold q2; rw [if_pos hsq]
  refine ⟨prof P (vStar P) (1 / 2), equil P hS hA _ _ hW0 hW (regBC_max P hS hA ht12 ht1), rfl, hp2,
    ?_, ?_, ?_⟩
  · intro v hv hvv
    have hvv' : t ≤ v := hvv
    have hcv : P.c ≤ P.d * P.sigma * v := by
      rw [hct]; nlinarith [mul_le_mul_of_nonneg_left hvv' hx.le]
    rw [hp2]
    refine ⟨(choice_optIn P _ _ _ _).2 (by show vStar P (1 / 2) ≤ v; rw [hvs12 ht12.le]; exact hvv'),
      ?_, ?_, ?_⟩
    · show keeps P v P.kL 1 (rr P v 1)
      rw [rr_eq P hS hA hv.1 1 hcv]; exact keeps_L P v 1
    · show keeps P v P.kH 1 (rr P v 1)
      rw [rr_eq P hS hA hv.1 1 hcv]; exact keeps_H P hS hv.1 1
    · show rr P v 1 = _
      rw [rr_eq P hS hA hv.1 1 hcv]; exact rL_one P hv.2
  · intro v hv h1 h2
    have h2' : v < t := h2
    rw [hp2]
    refine ⟨?_, by linarith⟩
    show (if vStar P (1 / 2) ≤ v then FirstChoice.optIn else if (1 / 2 : ℝ) ≤ v then FirstChoice.buy
      else FirstChoice.none) = .buy
    rw [hvs12 ht12.le, if_neg (not_le.2 h2'), if_pos h1]
  · intro v hv h
    rw [hp2]
    refine ⟨(choice_none P _ _ _ _).2 ⟨?_, ?_⟩, by linarith⟩
    · show v < vStar P (1 / 2); rw [hvs12 ht12.le]; linarith
    · show v < 1 / 2; exact h


lemma regC (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.d * P.sigma / Real.sqrt 2 < P.c ∧ P.c < P.d * P.sigma →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (P.mu - P.sigma) * v + 1 / 2 - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ s.p2 s.p1 ≤ v) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) := by
  have hd0 : 0 < P.d := hS.2.2.1
  have hd1 : P.d ≤ 1 := hS.2.2.2.1
  have hc0 : 0 ≤ P.c := hS.2.2.2.2
  have hsig : 0 < P.sigma := by unfold Params.sigma; linarith [hS.2.1]
  have hx : 0 < P.d * P.sigma := mul_pos hd0 hsig
  have hk : (2 + P.d) * P.sigma ≤ P.kL := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hdk : (2 + P.d) * (P.d * P.sigma) ≤ P.d * P.kL := by
    nlinarith [mul_le_mul_of_nonneg_left hk hd0.le]
  set t := P.c / (P.d * P.sigma) with htdef
  have hct : P.c = P.d * P.sigma * t := by
    rw [htdef, mul_div_assoc', mul_div_cancel_left₀ _ hx.ne']
  have ht0 : 0 ≤ t := div_nonneg hc0 hx.le
  have hD0 : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    have : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
      simp only [Params.mu, Params.sigma]; ring
    rw [this]; nlinarith
  have hD : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
    simp only [Params.mu, Params.sigma]; ring
  have hW := vStar_conds P hx
  have hW0 := vStar_nonneg P hS hx
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hvs12 : 1 / 2 ≤ t → vStar P (1 / 2) = t := by
    intro h
    unfold vStar; rw [← htdef]; apply max_eq_left
    rw [div_le_iff₀ (by linarith), hct]; nlinarith
  intro hcC
  obtain ⟨hcC1, hcC2⟩ := hcC
  have ht1 : t < 1 := by rw [hct] at hcC2; nlinarith
  rw [div_lt_iff₀ hs2, hct] at hcC1
  have hts : 1 < t * Real.sqrt 2 := by
    by_contra hc; push Not at hc; nlinarith [mul_le_mul_of_nonneg_left hc hx.le]
  have e : (t * Real.sqrt 2) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs2sq]; ring
  have hsq : ¬ t ^ 2 ≤ 1 / 2 := by intro h; nlinarith
  have ht12 : 1 / 2 < t := by
    by_contra hc; push Not at hc; apply hsq; nlinarith
  have hp2 : (prof P (vStar P) (1 / 2)).p2 (prof P (vStar P) (1 / 2)).p1 = 1 / 2 := by
    show q2 (min 1 (vStar P (1 / 2))) = 1 / 2
    rw [hvs12 ht12.le, min_eq_right ht1.le]; unfold q2; rw [if_neg hsq]
  refine ⟨prof P (vStar P) (1 / 2), equil P hS hA _ _ hW0 hW (regBC_max P hS hA ht12 ht1), rfl, hp2,
    ?_, ?_, ?_⟩
  · intro v hv hvv
    have hvv' : t ≤ v := hvv
    have hcv : P.c ≤ P.d * P.sigma * v := by
      rw [hct]; nlinarith [mul_le_mul_of_nonneg_left hvv' hx.le]
    rw [hp2]
    refine ⟨(choice_optIn P _ _ _ _).2 (by show vStar P (1 / 2) ≤ v; rw [hvs12 ht12.le]; exact hvv'),
      ?_, ?_, ?_⟩
    · show keeps P v P.kL (1 / 2) (rr P v (1 / 2))
      rw [rr_eq P hS hA hv.1 _ hcv]; exact keeps_L P v _
    · show keeps P v P.kH (1 / 2) (rr P v (1 / 2))
      rw [rr_eq P hS hA hv.1 _ hcv]; exact keeps_H P hS hv.1 _
    · show rr P v (1 / 2) = _
      rw [rr_eq P hS hA hv.1 _ hcv]; exact rL_half P (by linarith)
  · intro v hv h1 h2
    have h2' : v < t := h2
    rw [hp2]
    refine ⟨?_, h1⟩
    show (if vStar P (1 / 2) ≤ v then FirstChoice.optIn else if (1 / 2 : ℝ) ≤ v then FirstChoice.buy
      else FirstChoice.none) = .buy
    rw [hvs12 ht12.le, if_neg (not_le.2 h2'), if_pos h1]
  · intro v hv h
    rw [hp2]
    refine ⟨(choice_none P _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · show v < vStar P (1 / 2); rw [hvs12 ht12.le]; linarith
    · show v < 1 / 2; exact h


lemma regD (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.d * P.sigma ≤ P.c →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1,
          s.choice s.p1 v ≠ .optIn ∧
          (s.choice s.p1 v = .buy ↔ 1 / 2 ≤ v) ∧
          (s.p2 s.p1 ≤ v ↔ 1 / 2 ≤ v))) := by
  have hd0 : 0 < P.d := hS.2.2.1
  have hd1 : P.d ≤ 1 := hS.2.2.2.1
  have hc0 : 0 ≤ P.c := hS.2.2.2.2
  have hsig : 0 < P.sigma := by unfold Params.sigma; linarith [hS.2.1]
  have hx : 0 < P.d * P.sigma := mul_pos hd0 hsig
  have hk : (2 + P.d) * P.sigma ≤ P.kL := by
    have h := le_trans (le_max_left _ _) hA
    simp only [Params.mu, Params.sigma] at h ⊢; linarith
  have hdk : (2 + P.d) * (P.d * P.sigma) ≤ P.d * P.kL := by
    nlinarith [mul_le_mul_of_nonneg_left hk hd0.le]
  set t := P.c / (P.d * P.sigma) with htdef
  have hct : P.c = P.d * P.sigma * t := by
    rw [htdef, mul_div_assoc', mul_div_cancel_left₀ _ hx.ne']
  have ht0 : 0 ≤ t := div_nonneg hc0 hx.le
  have hD0 : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    have : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
      simp only [Params.mu, Params.sigma]; ring
    rw [this]; nlinarith
  have hD : 2 + P.d + P.d * P.mu + P.d * P.sigma = 2 + P.d + P.d * P.kL + 2 * (P.d * P.sigma) := by
    simp only [Params.mu, Params.sigma]; ring
  have hW := vStar_conds P hx
  have hW0 := vStar_nonneg P hS hx
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  intro hcD
  have hW0D : ∀ p1 : ℝ, 0 ≤ (fun _ : ℝ => (2 : ℝ)) p1 := fun _ => by norm_num
  have hWD : ∀ p1, ∀ v ∈ Icc (0 : ℝ) 1,
      ((fun _ : ℝ => (2 : ℝ)) p1 ≤ v →
        P.c ≤ P.d * P.sigma * v ∧ p1 ≤ (1 + P.d * P.sigma) * v - P.c) ∧
      (v < (fun _ : ℝ => (2 : ℝ)) p1 →
        P.d * P.sigma * v ≤ P.c ∨ (1 + P.d * P.sigma) * v - P.c < p1) := by
    intro p1 v hv
    refine ⟨fun h => ?_, fun _ => Or.inl ?_⟩
    · have h' : (2 : ℝ) ≤ v := h
      exact absurd hv.2 (by linarith)
    · nlinarith [mul_le_mul_of_nonneg_left hv.2 hx.le]
  have hmaxD : ∀ p1, Phi P (fun _ : ℝ => (2 : ℝ)) p1 ≤ Phi P (fun _ : ℝ => (2 : ℝ)) (1 / 2) := by
    intro p1
    unfold Phi
    have e : (1 / 2 : ℝ) * max (1 - max 0 (min 2 (1 / 2))) 0 = 1 / 4 := by norm_num
    rw [e]
    have key : p1 * max (1 - max 0 (min 2 p1)) 0 ≤ 1 / 4 := by
      rcases le_or_gt p1 0 with h0 | h0
      · rw [min_eq_right (by linarith), max_eq_left h0, sub_zero, max_eq_left zero_le_one]
        linarith
      · rcases le_or_gt p1 1 with h1 | h1
        · rw [min_eq_right (by linarith), max_eq_right h0.le, max_eq_left (by linarith)]
          nlinarith [sq_nonneg (p1 - 1 / 2)]
        · have : 1 ≤ max 0 (min 2 p1) := le_max_of_le_right (le_min (by norm_num) h1.le)
          rw [max_eq_right (by linarith)]; linarith
    linarith
  have hp2D : (prof P (fun _ : ℝ => (2 : ℝ)) (1 / 2)).p2
      (prof P (fun _ : ℝ => (2 : ℝ)) (1 / 2)).p1 = 1 / 2 := by
    show q2 (min 1 2) = 1 / 2
    unfold q2; norm_num
  refine ⟨prof P (fun _ : ℝ => (2 : ℝ)) (1 / 2), equil P hS hA _ _ hW0D hWD hmaxD, rfl, hp2D,
    fun v hv => ⟨?_, ?_, ?_⟩⟩
  · rw [Ne, choice_optIn]; show ¬ (2 : ℝ) ≤ v; linarith [hv.2]
  · show (if (2 : ℝ) ≤ v then FirstChoice.optIn else if (1 / 2 : ℝ) ≤ v then FirstChoice.buy
      else FirstChoice.none) = .buy ↔ _
    rw [if_neg (by linarith [hv.2])]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩
  · rw [hp2D]


end GDPRP1


open GDPRDataMarkets.Rights in
theorem solution (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    -- A. `0 ≤ c ≤ δσ/2`
    (P.c ≤ P.d * P.sigma / 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = P1star P ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v1star P ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < v1star P →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- B. `δσ/2 < c ≤ δσ/√2`
    (P.d * P.sigma / 2 < P.c ∧ P.c ≤ P.d * P.sigma / Real.sqrt 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ v < s.p2 s.p1) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- C. `δσ/√2 < c < δσ`
    (P.d * P.sigma / Real.sqrt 2 < P.c ∧ P.c < P.d * P.sigma →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (P.mu - P.sigma) * v + 1 / 2 - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ s.p2 s.p1 ≤ v) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- D. `c ≥ δσ`
    (P.d * P.sigma ≤ P.c →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1,
          s.choice s.p1 v ≠ .optIn ∧
          (s.choice s.p1 v = .buy ↔ 1 / 2 ≤ v) ∧
          (s.p2 s.p1 ≤ v ↔ 1 / 2 ≤ v))) := by
  exact ⟨GDPRP1.regA P hS hA, GDPRP1.regB P hS hA, GDPRP1.regC P hS hA, GDPRP1.regD P hS hA⟩
