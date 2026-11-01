-- Prove2me | solution 1 for CyberShare.Sharing.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:44:41.573716+00:00
-- url     : https://prove2.me/submissions/35113d36-1d7d-4cc4-b3dd-feeb45c6d76d

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

def outEquiv : Outcome ≃ Sig × Sig × Sig × Bool × Bool where
  toFun w := (w.st, w.y1, w.y2, w.attack1, w.attack2)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv w := by cases w; rfl
  right_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl

lemma sum_sig (f : Sig → ℝ) : ∑ s : Sig, f s = f .L + f .H := by
  have : (Finset.univ : Finset Sig) = {.L, .H} := rfl
  rw [this, Finset.sum_pair (by decide)]

lemma sum_outcome (f : Outcome → ℝ) :
    ∑ w : Outcome, f w = ∑ st : Sig, ∑ y1 : Sig, ∑ y2 : Sig, ∑ a1 : Bool, ∑ a2 : Bool,
      f ⟨st, y1, y2, a1, a2⟩ := by
  rw [← Equiv.sum_comp outEquiv.symm]
  simp [Fintype.sum_prod_type, outEquiv]

def al (P : Params) (o : Dec) (y y' : Sig) (st : Sig) : ℝ :=
  signalProb P st y * (if o = .N then 1 else signalProb P st y')

def ind (b : Bool) : ℝ := if b then 1 else 0

lemma cell_sum (P : Params) (o : Dec) (y y' : Sig) (g : Outcome → ℝ) :
    ∑ w ∈ cell1 o y y', prob P w * g w =
    ∑ st : Sig, ∑ y1 : Sig, ∑ y2 : Sig, ∑ a1 : Bool, ∑ a2 : Bool,
      (if y1 = y ∧ (o = .N ∨ y2 = y') then prob P ⟨st, y1, y2, a1, a2⟩ * g ⟨st, y1, y2, a1, a2⟩ else 0) := by
  rw [cell1, Finset.sum_filter, sum_outcome]

lemma cell_P (P : Params) (o : Dec) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w = (1 - P.rho) * al P o y y' .L + P.rho * al P o y y' .H := by
  have := cell_sum P o y y' (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  cases o <;> cases y <;> cases y' <;>
  simp [sum_sig, al, prob, prior, signalProb, attackProb, stateValue] <;> ring


lemma cell_S0 (P : Params) (o : Dec) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w * ind w.attack1 =
      (1 - P.rho) * P.thL * al P o y y' .L + P.rho * P.thH * al P o y y' .H := by
  rw [cell_sum]
  cases o <;> cases y <;> cases y' <;>
  simp [sum_sig, al, prob, prior, signalProb, attackProb, stateValue, ind] <;> ring

lemma cell_S2 (P : Params) (o : Dec) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 * ind w.attack2) =
      (1 - P.rho) * P.thL ^ 2 * al P o y y' .L + P.rho * P.thH ^ 2 * al P o y y' .H := by
  rw [cell_sum]
  cases o <;> cases y <;> cases y' <;>
  simp [sum_sig, al, prob, prior, signalProb, attackProb, stateValue, ind] <;> ring

def dd (P : Params) (att : Bool) (k : ℝ) : ℝ := if att then pos (P.delta - P.gamma * k) else 0
def Ae (P : Params) : ℝ := (P.a + (P.b - 1) * P.c) / (2 - P.b)
def eC (P : Params) : ℝ := (2 - P.b ^ 2) / (4 - P.b ^ 2)
def fC (P : Params) : ℝ := P.b / (4 - P.b ^ 2)

lemma core (a b c d1 d2 : ℝ) (hb : b ≤ 1) (hb0 : 0 ≤ b) :
    ((a + c) / (2 - b) + (2 * d1 + b * d2) / (4 - b ^ 2) - (c + d1)) *
      (a - ((a + c) / (2 - b) + (2 * d1 + b * d2) / (4 - b ^ 2)) +
        b * ((a + c) / (2 - b) + (2 * d2 + b * d1) / (4 - b ^ 2))) =
    ((a + (b - 1) * c) / (2 - b) - (2 - b ^ 2) / (4 - b ^ 2) * d1 + b / (4 - b ^ 2) * d2) ^ 2 := by
  have h1 : (2 - b) ≠ 0 := by linarith
  have h2 : (4 - b ^ 2) ≠ 0 := by nlinarith only [hb, hb0]
  set p := (a + c) / (2 - b) with hpdef
  set r := 1 / (4 - b ^ 2) with hrdef
  have hp : (2 - b) * p = a + c := by rw [hpdef]; field_simp
  have hr : (4 - b ^ 2) * r = 1 := by rw [hrdef]; field_simp
  have e1 : (2 * d1 + b * d2) / (4 - b ^ 2) = (2 * d1 + b * d2) * r := by rw [hrdef]; ring
  have e2 : (2 * d2 + b * d1) / (4 - b ^ 2) = (2 * d2 + b * d1) * r := by rw [hrdef]; ring
  have e3 : (a + (b - 1) * c) / (2 - b) = p - c := by
    rw [hpdef]; field_simp; ring
  have e4 : (2 - b ^ 2) / (4 - b ^ 2) = (2 - b ^ 2) * r := by rw [hrdef]; ring
  have e5 : b / (4 - b ^ 2) = b * r := by rw [hrdef]; ring
  rw [e1, e2, e3, e4, e5]
  clear_value p r
  linear_combination (d1 * (a - (p + (2 * d1 + b * d2) * r) + b * (p + (2 * d2 + b * d1) * r))) * hr +
    (-(p - c - (2 - b ^ 2) * r * d1 + b * r * d2)) * hp

lemma payoff1_eq (P : Params) (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (K1 K2 : Sig → Sig → ℝ) (w : Outcome) :
    payoff1 P K1 K2 w =
      (Ae P - eC P * dd P w.attack1 (K1 w.y1 w.y2) + fC P * dd P w.attack2 (K2 w.y2 w.y1)) ^ 2
        - P.kappa * (K1 w.y1 w.y2) ^ 2 := by
  unfold payoff1 profit pStar
  simp only [cost, dd, Ae, eC, fC]
  cases h1 : w.attack1 <;> cases h2 : w.attack2 <;> simp only [if_true, if_false, Bool.false_eq_true]
  all_goals
    have h1 : (2 - P.b) ≠ 0 := by linarith
    have h2 : (4 - P.b ^ 2) ≠ 0 := by nlinarith only [hb, hb0]
    generalize pos (P.delta - P.gamma * K1 w.y1 w.y2) = d1
    generalize pos (P.delta - P.gamma * K2 w.y2 w.y1) = d2
    field_simp
    ring

def Gabs (e g d k S0 S1 Pc U2 x : ℝ) : ℝ :=
  U2 - 2 * e * S1 * max (d - g * x) 0 + e ^ 2 * S0 * (max (d - g * x) 0) ^ 2 - k * Pc * x ^ 2

lemma quadId (e g d k S0 S1 Pc U2 x xs C : ℝ) (hCdef : C = k * Pc - e ^ 2 * g ^ 2 * S0)
    (hx : C * xs = e * g * (S1 - e * d * S0)) :
    U2 - 2 * e * S1 * (d - g * x) + e ^ 2 * S0 * (d - g * x) ^ 2 - k * Pc * x ^ 2 =
      (U2 - 2 * e * S1 * (d - g * xs) + e ^ 2 * S0 * (d - g * xs) ^ 2 - k * Pc * xs ^ 2) -
        C * (x - xs) ^ 2 := by
  subst hCdef
  linear_combination (-2 * (x - xs)) * hx

lemma maxQ (e g d k S0 S1 Pc U2 : ℝ) (he : 0 < e) (hg : 0 < g) (hS1 : 0 ≤ S1) (hS0 : 0 ≤ S0)
    (hC : 0 < k * Pc - e ^ 2 * g ^ 2 * S0)
    (hxs : g * (e * g * (S1 - e * d * S0) / (k * Pc - e ^ 2 * g ^ 2 * S0)) < d) (x : ℝ) :
    Gabs e g d k S0 S1 Pc U2 x ≤
      Gabs e g d k S0 S1 Pc U2 (e * g * (S1 - e * d * S0) / (k * Pc - e ^ 2 * g ^ 2 * S0))
        - (k * Pc - e ^ 2 * g ^ 2 * S0) *
          (x - e * g * (S1 - e * d * S0) / (k * Pc - e ^ 2 * g ^ 2 * S0)) ^ 2 := by
  set C := k * Pc - e ^ 2 * g ^ 2 * S0 with hCdef
  set xs := e * g * (S1 - e * d * S0) / C with hxsdef
  have hx : C * xs = e * g * (S1 - e * d * S0) := by
    rw [hxsdef]; field_simp
  have hGs : Gabs e g d k S0 S1 Pc U2 xs =
      U2 - 2 * e * S1 * (d - g * xs) + e ^ 2 * S0 * (d - g * xs) ^ 2 - k * Pc * xs ^ 2 := by
    unfold Gabs
    rw [max_eq_left (by linarith)]
  rw [hGs]
  have hq := quadId e g d k S0 S1 Pc U2 x xs C hCdef hx
  unfold Gabs
  by_cases hcase : 0 ≤ d - g * x
  · rw [max_eq_left hcase]
    linarith only [hq]
  · have hcase := not_le.mp hcase
    rw [max_eq_right hcase.le]
    have h1 : 0 ≤ e * S1 * (g * x - d) := by
      apply mul_nonneg (mul_nonneg he.le hS1); linarith
    have h2 : 0 ≤ e ^ 2 * S0 * (d - g * x) ^ 2 := by positivity
    have e3 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [e3]
    linarith only [hq, h1, h2]



/-! ## Parameter facts -/

section params
variable (P : Params)

lemma eC_pos (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) : 0 < eC P := by
  unfold eC
  apply div_pos <;> nlinarith

lemma eC_le (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) : eC P ≤ 1 / 2 := by
  unfold eC
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

lemma fC_nonneg (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) : 0 ≤ fC P := by
  unfold fC
  apply div_nonneg hb0; nlinarith

lemma fC_le (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) : fC P ≤ 1 / 3 := by
  unfold fC
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

lemma Ae_ge (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (hc : 0 ≤ P.c) (hca : P.c + P.delta < P.a)
    (hd : 0 < P.delta) : eC P * P.delta < Ae P := by
  have he := eC_le P hb hb0
  have he0 := eC_pos P hb hb0
  unfold Ae
  rw [lt_div_iff₀ (by linarith)]
  have h1 : eC P * P.delta * (2 - P.b) ≤ eC P * P.delta * 2 := by
    have : 0 ≤ eC P * P.delta := by positivity
    nlinarith
  have h2 : eC P * P.delta * 2 ≤ P.delta := by nlinarith
  linarith [mul_nonneg hb0 hc]

end params

/-! ## Cell facts -/

section cells

lemma sp_pos (P : Params) (hl0 : 1 / 2 < P.lam) (hl1 : P.lam < 1) (st y : Sig) :
    0 < signalProb P st y := by
  unfold signalProb; split_ifs <;> linarith

lemma al_pos (P : Params) (hl0 : 1 / 2 < P.lam) (hl1 : P.lam < 1) (o : Dec) (y y' st : Sig) :
    0 < al P o y y' st := by
  unfold al
  have := sp_pos P hl0 hl1 st y
  have := sp_pos P hl0 hl1 st y'
  split_ifs <;> positivity

lemma al_ratio (P : Params) (hl0 : 1 / 2 < P.lam) (hl1 : P.lam < 1) (o : Dec) (y y' : Sig) :
    (1 - P.lam) ^ 2 * al P o y y' .H ≤ P.lam ^ 2 * al P o y y' .L := by
  cases o <;> cases y <;> cases y' <;> simp [al, signalProb] <;>
  nlinarith [mul_pos (sub_pos.2 hl1) (sub_pos.2 hl1), mul_pos (by linarith : (0:ℝ) < P.lam) (sub_pos.2 hl1),
    mul_pos (mul_pos (by linarith : (0:ℝ) < P.lam) (sub_pos.2 hl1)) (sub_pos.2 hl1),
    mul_pos (mul_pos (by linarith : (0:ℝ) < P.lam) (by linarith : (0:ℝ) < P.lam)) (sub_pos.2 hl1)]

lemma cmp_abs (p q tL tH l aL aH : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : tL ≤ tH)
    (hr : (1 - l) ^ 2 * aH ≤ l ^ 2 * aL) :
    (p * tL * aL + q * tH * aH) * (p * (1 - l) ^ 2 + q * l ^ 2) ≤
      (p * tL * (1 - l) ^ 2 + q * tH * l ^ 2) * (p * aL + q * aH) := by
  have : 0 ≤ p * q * (tH - tL) * (l ^ 2 * aL - (1 - l) ^ 2 * aH) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg hp hq) (by linarith)) (by linarith)
  linear_combination this

end cells

section dl
variable (P : Params)

def R0 : ℝ := (1 - P.rho) * (1 - P.lam) ^ 2 + P.rho * P.lam ^ 2
def S00 : ℝ := (1 - P.rho) * P.thL * (1 - P.lam) ^ 2 + P.rho * P.thH * P.lam ^ 2
def S20 : ℝ := (1 - P.rho) * P.thL ^ 2 * (1 - P.lam) ^ 2 + P.rho * P.thH ^ 2 * P.lam ^ 2

lemma deltaLow_eq (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (hk : 0 < P.kappa)
    (hl0 : 1 / 2 < P.lam) (hl1 : P.lam < 1) (hr0 : 0 < P.rho) (hr1 : P.rho < 1) :
    deltaLow P = P.gamma ^ 2 * Ae P * (eC P * S00 P + fC P * S20 P) / (P.kappa * R0 P) := by
  have h1 : (2 - P.b) ≠ 0 := by linarith
  have h2 : (2 + P.b) ≠ 0 := by linarith
  have h3 : (4 - P.b ^ 2) ≠ 0 := by nlinarith only [hb, hb0]
  have h4 : 4 - P.b ^ 2 = (2 - P.b) * (2 + P.b) := by ring
  have hR : (2 * P.lam - 1) * P.rho + (1 - P.lam) ^ 2 = R0 P := by unfold R0; ring
  have hR0 : R0 P ≠ 0 := by
    unfold R0
    have : 0 < (1 - P.rho) * (1 - P.lam) ^ 2 := by
      apply mul_pos (by linarith); apply pow_pos; linarith
    have : 0 < P.rho * P.lam ^ 2 := by positivity
    linarith
  unfold deltaLow Ae eC fC S00 S20
  rw [hR]
  rw [h4] at *
  have hk' : P.kappa ≠ 0 := hk.ne'
  field_simp
  ring

end dl

/-! ## Cell objective -/

section obj
variable (P : Params)

def uu (B : Sig → Sig → ℝ) (w : Outcome) : ℝ := Ae P + fC P * dd P w.attack2 (B w.y2 w.y1)

def S0c (o : Dec) (y y' : Sig) : ℝ := ∑ w ∈ cell1 o y y', prob P w * ind w.attack1
def Pcc (o : Dec) (y y' : Sig) : ℝ := ∑ w ∈ cell1 o y y', prob P w
def S2c (o : Dec) (y y' : Sig) : ℝ := ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 * ind w.attack2)
def S1c (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) : ℝ :=
  ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 * uu P B w)
def U2c (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) : ℝ :=
  ∑ w ∈ cell1 o y y', prob P w * (uu P B w) ^ 2

lemma ind_sq (b : Bool) : ind b * ind b = ind b := by cases b <;> simp [ind]

lemma dd_ind (att : Bool) (x : ℝ) : dd P att x = ind att * max (P.delta - P.gamma * x) 0 := by
  cases att <;> simp [dd, ind, pos]

lemma mem_cell {o : Dec} {y y' : Sig} {w : Outcome} (h : w ∈ cell1 o y y') :
    w.y1 = y ∧ (o = .N ∨ w.y2 = y') := by
  simpa [cell1] using h

lemma dev1_cell (o : Dec) (A : Sig → Sig → ℝ) (y y' : Sig) (x : ℝ) {w : Outcome}
    (h : w ∈ cell1 o y y') : dev1 o A y y' x w.y1 w.y2 = x := by
  unfold dev1
  rw [if_pos (mem_cell h)]

lemma obj_eq (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (o : Dec) (A B : Sig → Sig → ℝ) (y y' : Sig) (x : ℝ) :
    ∑ w ∈ cell1 o y y', prob P w * payoff1 P (dev1 o A y y' x) B w =
      Gabs (eC P) P.gamma P.delta P.kappa (S0c P o y y') (S1c P o y y' B) (Pcc P o y y')
        (U2c P o y y' B) x := by
  unfold Gabs S0c S1c Pcc U2c
  set t := max (P.delta - P.gamma * x) 0
  have : ∀ w ∈ cell1 o y y', prob P w * payoff1 P (dev1 o A y y' x) B w =
      prob P w * (uu P B w) ^ 2 - 2 * eC P * t * (prob P w * (ind w.attack1 * uu P B w))
        + (eC P) ^ 2 * t ^ 2 * (prob P w * ind w.attack1) - P.kappa * x ^ 2 * prob P w := by
    intro w hw
    rw [payoff1_eq P hb hb0, dev1_cell o A y y' x hw, dd_ind]
    have := ind_sq w.attack1
    unfold uu
    simp only [dd_ind]
    -- ring with ind^2 = ind
    have h2 : (ind w.attack1) ^ 2 = ind w.attack1 := by linarith
    linear_combination (prob P w * (eC P) ^ 2 * t ^ 2) * h2
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end obj

/-! ## Best response -/

def Hy (P : Params) : Prop := P.Standing ∧ 2 * P.gamma ^ 2 < P.kappa ∧ deltaLow P < P.delta

def br (P : Params) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) : ℝ :=
  eC P * P.gamma * (S1c P o y y' B - eC P * P.delta * S0c P o y y') /
    (P.kappa * Pcc P o y y' - (eC P) ^ 2 * P.gamma ^ 2 * S0c P o y y')

section hy
variable {P : Params}

lemma prob_nonneg (h : P.Standing) (w : Outcome) : 0 ≤ prob P w := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hsp : ∀ st y, 0 ≤ signalProb P st y := fun st y => (sp_pos P hl0 hl1 st y).le
  have hat : ∀ st a, 0 ≤ attackProb P st a := by
    intro st a
    unfold attackProb stateValue
    cases st <;> cases a <;> simp <;> linarith
  have hpr : ∀ st, 0 ≤ prior P st := by
    intro st; unfold prior; cases st <;> simp <;> linarith
  unfold prob
  have := hsp w.st w.y1; have := hsp w.st w.y2; have := hat w.st w.attack1
  have := hat w.st w.attack2; have := hpr w.st
  positivity

lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

lemma dd_nonneg (att : Bool) (x : ℝ) : 0 ≤ dd P att x := by
  unfold dd pos; split_ifs <;> simp

lemma dd_le (hd : 0 < P.delta) (hg : 0 < P.gamma) (att : Bool) {x : ℝ} (hx : 0 ≤ x) :
    dd P att x ≤ ind att * P.delta := by
  cases att
  · simp [dd, ind]
  · simp only [dd, ind, pos, if_true, one_mul]
    exact max_le (by linarith [mul_nonneg hg.le hx]) hd.le

lemma cell_facts (h : P.Standing) (o : Dec) (y y' : Sig) :
    0 < Pcc P o y y' ∧ 0 < S0c P o y y' ∧ S0c P o y y' ≤ Pcc P o y y' ∧
    S2c P o y y' ≤ S0c P o y y' ∧
    S0c P o y y' * R0 P ≤ S00 P * Pcc P o y y' ∧
    S2c P o y y' * R0 P ≤ S20 P * Pcc P o y y' := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have e1 : Pcc P o y y' = (1 - P.rho) * al P o y y' .L + P.rho * al P o y y' .H := cell_P P o y y'
  have e2 : S0c P o y y' = (1 - P.rho) * P.thL * al P o y y' .L + P.rho * P.thH * al P o y y' .H :=
    cell_S0 P o y y'
  have e3 : S2c P o y y' = (1 - P.rho) * P.thL ^ 2 * al P o y y' .L + P.rho * P.thH ^ 2 * al P o y y' .H :=
    cell_S2 P o y y'
  have aL := al_pos P hl0 hl1 o y y' .L
  have aH := al_pos P hl0 hl1 o y y' .H
  have rat := al_ratio P hl0 hl1 o y y'
  have r1 : 0 < 1 - P.rho := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; positivity
  · rw [e2]; have : 0 < P.thH := by linarith
    positivity
  · rw [e1, e2]; linarith [mul_pos r1 aL, mul_pos hr0 aH, mul_nonneg (mul_pos r1 aL).le (by linarith : 0 ≤ 1 - P.thL),
      mul_nonneg (mul_pos hr0 aH).le (by linarith : 0 ≤ 1 - P.thH)]
  · rw [e2, e3]
    have h1 : P.thL ^ 2 ≤ P.thL := by nlinarith only [hL, hLH, hH1]
    have h2 : P.thH ^ 2 ≤ P.thH := by nlinarith only [hL, hLH, hH1]
    linarith [mul_nonneg (mul_pos r1 aL).le (sub_nonneg.2 h1), mul_nonneg (mul_pos hr0 aH).le (sub_nonneg.2 h2)]
  · rw [e1, e2]
    have := cmp_abs (1 - P.rho) P.rho P.thL P.thH P.lam (al P o y y' .L) (al P o y y' .H) r1.le hr0.le hLH.le rat
    unfold S00 R0
    linarith [this]
  · rw [e1, e3]
    have := cmp_abs (1 - P.rho) P.rho (P.thL ^ 2) (P.thH ^ 2) P.lam (al P o y y' .L) (al P o y y' .H) r1.le hr0.le
      (by nlinarith only [hL, hLH]) rat
    unfold S20 R0
    linarith [this]

end hy

section hy2
variable {P : Params}

lemma S1_lower (h : P.Standing) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) :
    Ae P * S0c P o y y' ≤ S1c P o y y' B := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hf := fC_nonneg P hb1 hb0
  unfold S0c S1c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have hp := prob_nonneg (P := P) ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ w
  have hi := ind_nonneg w.attack1
  have hdd := dd_nonneg (P := P) w.attack2 (B w.y2 w.y1)
  unfold uu
  linarith [mul_nonneg hf hdd, mul_nonneg hp hi, mul_nonneg (mul_nonneg hp hi) (mul_nonneg hf hdd)]

lemma S1_upper (h : P.Standing) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ)
    (hB : ∀ z z', 0 ≤ B z z') :
    S1c P o y y' B ≤ Ae P * S0c P o y y' + fC P * P.delta * S2c P o y y' := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hf := fC_nonneg P hb1 hb0
  unfold S0c S1c S2c
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hp := prob_nonneg (P := P) ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ w
  have hi := ind_nonneg w.attack1
  have hdd := dd_le (P := P) hd hg w.attack2 (hB w.y2 w.y1)
  unfold uu
  have h3 : fC P * dd P w.attack2 (B w.y2 w.y1) ≤ fC P * (ind w.attack2 * P.delta) :=
    mul_le_mul_of_nonneg_left hdd hf
  have h4 : 0 ≤ prob P w * ind w.attack1 := mul_nonneg hp hi
  linarith [mul_le_mul_of_nonneg_left h3 h4]

lemma Cq_pos (h : Hy P) (o : Dec) (y y' : Sig) :
    0 < P.kappa * Pcc P o y y' - (eC P) ^ 2 * P.gamma ^ 2 * S0c P o y y' := by
  obtain ⟨hS, hk2, _⟩ := h
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := hS
  obtain ⟨hP, hS0, hle, -⟩ := cell_facts ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have : (eC P) ^ 2 ≤ 1 / 4 := by nlinarith only [he, he0]
  have hg2 : 0 < P.gamma ^ 2 := by positivity
  linarith [mul_le_mul_of_nonneg_right this (mul_nonneg hg2.le hS0.le), mul_nonneg hg2.le (sub_nonneg.2 hle),
    mul_pos hP hg2, mul_lt_mul_of_pos_right hk2 hP]

lemma br_bounds (h : Hy P) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (hB : ∀ z z', 0 ≤ B z z') :
    0 ≤ S1c P o y y' B ∧ 0 < br P o y y' B ∧ P.gamma * br P o y y' B < P.delta := by
  have hC := Cq_pos h o y y'
  obtain ⟨hS, hk2, hlow⟩ := h
  have hS' := hS
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := hS
  obtain ⟨hP, hS0, hle, hS2, c0, c2⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hA := Ae_ge P hb1 hb0 hc hcd hd
  have s1l := S1_lower hS' o y y' B
  have s1u := S1_upper hS' o y y' B hB
  have hA0 : 0 < Ae P := lt_trans (by positivity) hA
  have hS1 : 0 ≤ S1c P o y y' B := by linarith [mul_pos hA0 hS0]
  have hR0 : 0 < R0 P := by
    unfold R0
    have : 0 < (1 - P.rho) * (1 - P.lam) ^ 2 := by
      apply mul_pos (by linarith); apply pow_pos; linarith
    have : 0 < P.rho * P.lam ^ 2 := by positivity
    linarith
  refine ⟨hS1, ?_, ?_⟩
  · unfold br
    apply div_pos _ hC
    have hAd : 0 < Ae P - eC P * P.delta := by linarith
    have : 0 < eC P * P.gamma := by positivity
    apply mul_pos this
    linarith [mul_pos hAd hS0, s1l]
  · -- key inequality
    have hdl := deltaLow_eq P hb1 hb0 hk hl0 hl1 hr0 hr1
    have hkey : P.gamma ^ 2 * Ae P * (eC P * S00 P + fC P * S20 P) < P.delta * (P.kappa * R0 P) := by
      rw [hdl, div_lt_iff₀ (by positivity)] at hlow
      linarith
    have hS00 : 0 ≤ S00 P := by
      unfold S00
      have : 0 < P.thH := by linarith
      have : 0 < 1 - P.rho := by linarith
      positivity
    have hS20 : 0 ≤ S20 P := by
      unfold S20
      have : 0 < 1 - P.rho := by linarith
      positivity
    have step1 : R0 P * S1c P o y y' B ≤
        Ae P * (S00 P * Pcc P o y y') + fC P * P.delta * (S20 P * Pcc P o y y') := by
      have := mul_le_mul_of_nonneg_left s1u hR0.le
      linarith [mul_le_mul_of_nonneg_left c0 (hA0.le),
        mul_le_mul_of_nonneg_left c2 (mul_nonneg hf hd.le)]
    have step2 : P.gamma ^ 2 * eC P * (R0 P * S1c P o y y' B) ≤
        P.gamma ^ 2 * Ae P * (eC P * S00 P + fC P * S20 P) * Pcc P o y y' := by
      have g2 : 0 < P.gamma ^ 2 := by positivity
      have h1 := mul_le_mul_of_nonneg_left step1 (mul_nonneg g2.le he0.le)
      have h2 : eC P * P.delta ≤ Ae P := hA.le
      have h3 : 0 ≤ P.gamma ^ 2 * fC P * S20 P * Pcc P o y y' := by positivity
      have h4 := mul_nonneg h3 (sub_nonneg.2 h2)
      linarith only [h1, h4]
    have step3 : R0 P * (P.gamma ^ 2 * eC P * S1c P o y y' B) < R0 P * (P.delta * P.kappa * Pcc P o y y') := by
      have := mul_lt_mul_of_pos_right hkey hP
      linarith only [this, step2]
    have step4 := lt_of_mul_lt_mul_left step3 hR0.le
    unfold br
    have e1 : P.gamma * (eC P * P.gamma * (S1c P o y y' B - eC P * P.delta * S0c P o y y') /
        (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y')) =
        (P.gamma ^ 2 * eC P * (S1c P o y y' B - eC P * P.delta * S0c P o y y')) /
        (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') := by
      field_simp
    rw [e1, div_lt_iff₀ hC]
    linarith only [step4]

end hy2

def Best1 (P : Params) (o : Dec) (A B : Sig → Sig → ℝ) : Prop :=
  ∀ y y' x, 0 ≤ x →
    (∑ w ∈ cell1 o y y', prob P w * payoff1 P (dev1 o A y y' x) B w) ≤
    (∑ w ∈ cell1 o y y', prob P w * payoff1 P A B w)

lemma payoff1_congr (P : Params) (K K' B : Sig → Sig → ℝ) (w : Outcome)
    (h : K w.y1 w.y2 = K' w.y1 w.y2) : payoff1 P K B w = payoff1 P K' B w := by
  unfold payoff1; simp only [h]

lemma cur_eq {P : Params} (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (o : Dec) (A B : Sig → Sig → ℝ)
    (hA : Adapted o A) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w * payoff1 P A B w =
      Gabs (eC P) P.gamma P.delta P.kappa (S0c P o y y') (S1c P o y y' B) (Pcc P o y y')
        (U2c P o y y' B) (A y y') := by
  rw [← obj_eq P hb hb0 o A B y y' (A y y')]
  apply Finset.sum_congr rfl
  intro w hw
  rw [payoff1_congr P A (dev1 o A y y' (A y y')) B w]
  rw [dev1_cell o A y y' _ hw]
  obtain ⟨h1, h2⟩ := mem_cell hw
  rcases h2 with h2 | h2
  · have := hA h2 y w.y2 y'
    rw [h1]; exact this
  · rw [h1, h2]

lemma best1_iff {P : Params} (h : Hy P) (o : Dec) (A B : Sig → Sig → ℝ)
    (hA : Adapted o A) (hB : ∀ z z', 0 ≤ B z z') :
    Best1 P o A B ↔ ∀ y y', A y y' = br P o y y' B := by
  have hb1 := h.1.2.2.1
  have hb0 := h.1.2.1
  have hg := h.1.1.2.1
  have he0 := eC_pos P hb1 hb0
  constructor
  · intro hbest y y'
    obtain ⟨hS1, hpos, hlt⟩ := br_bounds h o y y' B hB
    have hC := Cq_pos h o y y'
    have hS0 := (cell_facts h.1 o y y').2.1
    have m := maxQ (eC P) P.gamma P.delta P.kappa (S0c P o y y') (S1c P o y y' B) (Pcc P o y y')
      (U2c P o y y' B) he0 hg hS1 hS0.le hC hlt (A y y')
    have hx := hbest y y' (br P o y y' B) hpos.le
    rw [obj_eq P hb1 hb0, cur_eq hb1 hb0 o A B hA] at hx
    have : (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') *
        (A y y' - br P o y y' B) ^ 2 ≤ 0 := by
      unfold br at hx ⊢
      linarith
    have h2 : (A y y' - br P o y y' B) ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      linarith [mul_pos hC hcon]
    have : A y y' - br P o y y' B = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (sq_nonneg _))
    linarith
  · intro hbr y y' x hx
    obtain ⟨hS1, hpos, hlt⟩ := br_bounds h o y y' B hB
    have hC := Cq_pos h o y y'
    have hS0 := (cell_facts h.1 o y y').2.1
    have m := maxQ (eC P) P.gamma P.delta P.kappa (S0c P o y y') (S1c P o y y' B) (Pcc P o y y')
      (U2c P o y y' B) he0 hg hS1 hS0.le hC hlt x
    rw [obj_eq P hb1 hb0, cur_eq hb1 hb0 o A B hA, hbr y y']
    unfold br at m ⊢
    linarith [mul_nonneg hC.le (sq_nonneg (x - eC P * P.gamma * (S1c P o y y' B - eC P * P.delta * S0c P o y y') /
      (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y')))]

/-! ## Symmetry (firm 2 clause) -/

def sw (w : Outcome) : Outcome := ⟨w.st, w.y2, w.y1, w.attack2, w.attack1⟩

lemma sw_sw (w : Outcome) : sw (sw w) = w := by cases w; rfl

lemma prob_sw (P : Params) (w : Outcome) : prob P (sw w) = prob P w := by
  unfold prob sw; simp only []; ring

lemma payoff2_sw (P : Params) (A B : Sig → Sig → ℝ) (w : Outcome) :
    payoff2 P A B (sw w) = payoff1 P B A w := rfl

lemma sum_cell_sw (o : Dec) (y y' : Sig) (f : Outcome → ℝ) :
    ∑ w ∈ cell2 o y y', f w = ∑ w ∈ cell1 o y y', f (sw w) := by
  apply Finset.sum_nbij' sw sw
  · intro w hw; simp only [cell1, cell2, sw, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    tauto
  · intro w hw; simp only [cell1, cell2, sw, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    tauto
  · intro w _; exact sw_sw w
  · intro w _; exact sw_sw w
  · intro w _; rfl

lemma key (P : Params) (o : Dec) (A B : Sig → Sig → ℝ) (y y' : Sig) :
    ∑ w ∈ cell2 o y y', prob P w * payoff2 P A B w =
      ∑ w ∈ cell1 o y y', prob P w * payoff1 P B A w := by
  rw [sum_cell_sw o y y']
  apply Finset.sum_congr rfl
  intro w _
  rw [prob_sw, payoff2_sw]

lemma invEq_iff_best (P : Params) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ) :
    IsInvEq P s1 s2 K1 K2 ↔ Adapted s2 K1 ∧ Adapted s1 K2 ∧ (∀ y y', 0 ≤ K1 y y' ∧ 0 ≤ K2 y y') ∧
      Best1 P s2 K1 K2 ∧ Best1 P s1 K2 K1 := by
  unfold IsInvEq Best1
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro y y' x hx
    have := h5 y y' x hx
    rw [key, key] at this
    exact this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro y y' x hx
    rw [key, key]
    exact h5 y y' x hx

/-! ## Fixed point formulation -/

lemma cell1_N (y y' y'' : Sig) : cell1 .N y y' = cell1 .N y y'' := by
  ext w; simp [cell1]

lemma br_adapted (P : Params) (B : Sig → Sig → ℝ) :
    Adapted .N (fun y y' => br P .N y y' B) := by
  intro _ y y' y''
  simp only [br, S0c, S1c, Pcc, cell1_N y y' y'']

lemma br_adapted' (P : Params) (o : Dec) (B : Sig → Sig → ℝ) :
    Adapted o (fun y y' => br P o y y' B) := by
  cases o
  · intro h; exact absurd h (by decide)
  · exact br_adapted P B

lemma br_pos_any {P : Params} (h : Hy P) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) :
    0 < br P o y y' B := by
  have hC := Cq_pos h o y y'
  have hS' := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨hP, hS0, hle, hS2, c0, c2⟩ := cell_facts hS' o y y'
  have he0 := eC_pos P hb1 hb0
  have hA := Ae_ge P hb1 hb0 hc hcd hd
  have s1l := S1_lower hS' o y y' B
  unfold br
  apply div_pos _ hC
  have h1 : 0 < Ae P - eC P * P.delta := by linarith
  have h2 : 0 < eC P * P.gamma := by positivity
  apply mul_pos h2
  linarith [mul_pos h1 hS0]

lemma invEq_iff {P : Params} (h : Hy P) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ) :
    IsInvEq P s1 s2 K1 K2 ↔ Adapted s2 K1 ∧ Adapted s1 K2 ∧ (∀ y y', 0 ≤ K1 y y' ∧ 0 ≤ K2 y y') ∧
      (∀ y y', K1 y y' = br P s2 y y' K2) ∧ (∀ y y', K2 y y' = br P s1 y y' K1) := by
  rw [invEq_iff_best]
  constructor
  · rintro ⟨a1, a2, n, b1, b2⟩
    exact ⟨a1, a2, n, (best1_iff h s2 K1 K2 a1 (fun z z' => (n z z').2)).1 b1,
      (best1_iff h s1 K2 K1 a2 (fun z z' => (n z z').1)).1 b2⟩
  · rintro ⟨a1, a2, n, b1, b2⟩
    exact ⟨a1, a2, n, (best1_iff h s2 K1 K2 a1 (fun z z' => (n z z').2)).2 b1,
      (best1_iff h s1 K2 K1 a2 (fun z z' => (n z z').1)).2 b2⟩

/-! ## Lipschitz -/

lemma dd_lip (P : Params) (hg : 0 < P.gamma) (att : Bool) (x x' : ℝ) :
    |dd P att x - dd P att x'| ≤ P.gamma * |x - x'| := by
  cases att
  · simp [dd]; positivity
  · simp only [dd, pos, if_true]
    calc |max (P.delta - P.gamma * x) 0 - max (P.delta - P.gamma * x') 0|
        ≤ |(P.delta - P.gamma * x) - (P.delta - P.gamma * x')| := abs_max_sub_max_le_abs _ _ _
      _ = P.gamma * |x - x'| := by
        rw [show (P.delta - P.gamma * x) - (P.delta - P.gamma * x') = -(P.gamma * (x - x')) by ring,
          abs_neg, abs_mul, abs_of_pos hg]

lemma ind_le (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

lemma S1_diff {P : Params} (h : P.Standing) (o : Dec) (y y' : Sig) (B B' : Sig → Sig → ℝ) (M : ℝ)
    (hM : ∀ z z', |B z z' - B' z z'| ≤ M) :
    |S1c P o y y' B - S1c P o y y' B'| ≤ fC P * P.gamma * M * Pcc P o y y' := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hf := fC_nonneg P hb1 hb0
  unfold S1c Pcc
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro w _
  have hp := prob_nonneg (P := P) ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ w
  have hi := ind_nonneg w.attack1
  have hi1 := ind_le w.attack1
  have hdl := dd_lip P hg w.attack2 (B w.y2 w.y1) (B' w.y2 w.y1)
  have hm := hM w.y2 w.y1
  have e1 : prob P w * (ind w.attack1 * uu P B w) - prob P w * (ind w.attack1 * uu P B' w) =
      prob P w * (ind w.attack1 * (fC P * (dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)))) := by
    unfold uu; ring
  rw [e1, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hi, abs_of_nonneg hf]
  have h2 : |dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)| ≤ P.gamma * M :=
    hdl.trans (mul_le_mul_of_nonneg_left hm hg.le)
  have h3 : ind w.attack1 * (fC P * |dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)|) ≤
      fC P * P.gamma * M := by
    have : fC P * |dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)| ≤ fC P * (P.gamma * M) :=
      mul_le_mul_of_nonneg_left h2 hf
    have h4 : 0 ≤ fC P * |dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)| :=
      mul_nonneg hf (abs_nonneg _)
    calc _ ≤ 1 * (fC P * |dd P w.attack2 (B w.y2 w.y1) - dd P w.attack2 (B' w.y2 w.y1)|) :=
          mul_le_mul_of_nonneg_right hi1 h4
      _ ≤ fC P * (P.gamma * M) := by linarith
      _ = _ := by ring
  calc _ ≤ prob P w * (fC P * P.gamma * M) := mul_le_mul_of_nonneg_left h3 hp
    _ = _ := by ring

lemma br_lip {P : Params} (h : Hy P) (o : Dec) (y y' : Sig) (B B' : Sig → Sig → ℝ) (M : ℝ)
    (hM : ∀ z z', |B z z' - B' z z'| ≤ M) :
    |br P o y y' B - br P o y y' B'| ≤ M / 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM .L .L)
  have hC := Cq_pos h o y y'
  have hS' := h.1
  obtain ⟨hk2, _⟩ := h.2
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨hP, hS0, hle, hS2, c0, c2⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hf3 := fC_le P hb1 hb0
  have hd1 := S1_diff hS' o y y' B B' M hM
  have e1 : br P o y y' B - br P o y y' B' =
      eC P * P.gamma * (S1c P o y y' B - S1c P o y y' B') /
        (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') := by
    unfold br; ring
  rw [e1, abs_div, abs_of_pos hC, div_le_iff₀ hC, abs_mul, abs_of_pos (by positivity : 0 < eC P * P.gamma)]
  have hg2 : 0 < P.gamma ^ 2 := by positivity
  have hee : eC P ^ 2 ≤ 1 / 4 := by nlinarith only [he, he0]
  have hef : eC P * fC P ≤ 1 / 6 := by nlinarith only [he, he0, hf, hf3]
  -- key: 2 e f γ² Pcc ≤ Cq
  have k1 : eC P * P.gamma * (|S1c P o y y' B - S1c P o y y' B'|) ≤
      eC P * P.gamma * (fC P * P.gamma * M * Pcc P o y y') :=
    mul_le_mul_of_nonneg_left hd1 (by positivity)
  have k2 : eC P * P.gamma * (fC P * P.gamma * M * Pcc P o y y') =
      (eC P * fC P) * P.gamma ^ 2 * (M * Pcc P o y y') := by ring
  have k3 : (eC P * fC P) * P.gamma ^ 2 * (M * Pcc P o y y') ≤ (1 / 6) * P.gamma ^ 2 * (M * Pcc P o y y') := by
    have : 0 ≤ P.gamma ^ 2 * (M * Pcc P o y y') := by positivity
    have := mul_le_mul_of_nonneg_right hef this
    linarith only [this]
  have k4 : M / 2 * (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') ≥
      (1 / 6) * P.gamma ^ 2 * (M * Pcc P o y y') := by
    have h5 : eC P ^ 2 * P.gamma ^ 2 * S0c P o y y' ≤ (1 / 4) * P.gamma ^ 2 * Pcc P o y y' := by
      have h1 := mul_le_mul_of_nonneg_right hee (mul_nonneg hg2.le hS0.le)
      have h2 := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ (1 / 4) * P.gamma ^ 2)
      linarith only [h1, h2]
    have h6 : P.gamma ^ 2 * Pcc P o y y' * 2 ≤ P.kappa * Pcc P o y y' := by
      have := mul_le_mul_of_nonneg_right hk2.le hP.le
      linarith only [this]
    have h7 : (7 / 4) * (P.gamma ^ 2 * Pcc P o y y') ≤
        P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y' := by
      linarith only [h5, h6]
    have h8 := mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ M / 2)
    have h9 : 0 ≤ M * (P.gamma ^ 2 * Pcc P o y y') := by positivity
    linarith only [h8, h9]
  linarith

/-! ## Contraction -/

abbrev XX := (Sig → Sig → ℝ) × (Sig → Sig → ℝ)

def Phi (P : Params) (s1 s2 : Dec) (p : XX) : XX :=
  (fun y y' => br P s2 y y' p.2, fun y y' => br P s1 y y' p.1)

lemma Phi_dist {P : Params} (h : Hy P) (s1 s2 : Dec) (p q : XX) :
    dist (Phi P s1 s2 p) (Phi P s1 s2 q) ≤ dist p q / 2 := by
  have hM0 : 0 ≤ dist p q := dist_nonneg
  have h1 : ∀ z z', |p.1 z z' - q.1 z z'| ≤ dist p q := by
    intro z z'
    have a1 : dist (p.1 z z') (q.1 z z') ≤ dist (p.1 z) (q.1 z) := dist_le_pi_dist (p.1 z) (q.1 z) z'
    have a2 : dist (p.1 z) (q.1 z) ≤ dist p.1 q.1 := dist_le_pi_dist p.1 q.1 z
    have a3 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
    rw [← Real.dist_eq]; linarith
  have h2 : ∀ z z', |p.2 z z' - q.2 z z'| ≤ dist p q := by
    intro z z'
    have a1 : dist (p.2 z z') (q.2 z z') ≤ dist (p.2 z) (q.2 z) := dist_le_pi_dist (p.2 z) (q.2 z) z'
    have a2 : dist (p.2 z) (q.2 z) ≤ dist p.2 q.2 := dist_le_pi_dist p.2 q.2 z
    have a3 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    rw [← Real.dist_eq]; linarith
  rw [Prod.dist_eq]
  apply max_le
  · apply (dist_pi_le_iff (by positivity)).2
    intro z
    apply (dist_pi_le_iff (by positivity)).2
    intro z'
    rw [Real.dist_eq]
    exact br_lip h s2 z z' p.2 q.2 _ h2
  · apply (dist_pi_le_iff (by positivity)).2
    intro z
    apply (dist_pi_le_iff (by positivity)).2
    intro z'
    rw [Real.dist_eq]
    exact br_lip h s1 z z' p.1 q.1 _ h1

lemma Phi_contr {P : Params} (h : Hy P) (s1 s2 : Dec) :
    ContractingWith (1 / 2 : NNReal) (Phi P s1 s2) := by
  refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have := Phi_dist h s1 s2 p q
  have e : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [e]; linarith

lemma exists_unique_inv {P : Params} (h : Hy P) (s1 s2 : Dec) :
    ∃ pair : XX, IsInvEq P s1 s2 pair.1 pair.2 ∧
      (∀ y y' : Sig, 0 < pair.1 y y' ∧ pair.1 y y' < P.delta / P.gamma ∧
        0 < pair.2 y y' ∧ pair.2 y y' < P.delta / P.gamma) ∧
      ∀ pair' : XX, IsInvEq P s1 s2 pair'.1 pair'.2 → pair' = pair := by
  have hc := Phi_contr h s1 s2
  have hg : 0 < P.gamma := h.1.1.2.1
  set p := ContractingWith.fixedPoint (Phi P s1 s2) hc with hpdef
  have hp : Phi P s1 s2 p = p := ContractingWith.fixedPoint_isFixedPt hc
  have hp1 : ∀ y y', p.1 y y' = br P s2 y y' p.2 := by
    intro y y'
    have := congrFun (congrFun (congrArg Prod.fst hp) y) y'
    exact this.symm
  have hp2 : ∀ y y', p.2 y y' = br P s1 y y' p.1 := by
    intro y y'
    have := congrFun (congrFun (congrArg Prod.snd hp) y) y'
    exact this.symm
  have pos1 : ∀ y y', 0 < p.1 y y' := fun y y' => by rw [hp1]; exact br_pos_any h _ _ _ _
  have pos2 : ∀ y y', 0 < p.2 y y' := fun y y' => by rw [hp2]; exact br_pos_any h _ _ _ _
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [invEq_iff h]
    refine ⟨?_, ?_, fun y y' => ⟨(pos1 y y').le, (pos2 y y').le⟩, hp1, hp2⟩
    · have : p.1 = fun y y' => br P s2 y y' p.2 := funext fun y => funext fun y' => hp1 y y'
      rw [this]; exact br_adapted' P s2 p.2
    · have : p.2 = fun y y' => br P s1 y y' p.1 := funext fun y => funext fun y' => hp2 y y'
      rw [this]; exact br_adapted' P s1 p.1
  · intro y y'
    refine ⟨pos1 y y', ?_, pos2 y y', ?_⟩
    · rw [lt_div_iff₀ hg, hp1]
      have := (br_bounds h s2 y y' p.2 (fun z z' => (pos2 z z').le)).2.2
      linarith
    · rw [lt_div_iff₀ hg, hp2]
      have := (br_bounds h s1 y y' p.1 (fun z z' => (pos1 z z').le)).2.2
      linarith
  · intro q hq
    rw [invEq_iff h] at hq
    obtain ⟨-, -, -, q1, q2⟩ := hq
    have hq : Phi P s1 s2 q = q := by
      ext y y'
      · exact (q1 y y').symm
      · exact (q2 y y').symm
    have := Phi_dist h s1 s2 q p
    rw [hq, hp] at this
    have h0 : dist q p = 0 := by
      have := dist_nonneg (x := q) (y := p)
      linarith
    exact dist_eq_zero.1 h0

lemma deltaLow_bounds (P : Params) (hbase : BaseStanding P.a P.c P.gamma P.thL P.thH P.rho P.lam)
    (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hk : P.gamma ^ 2 * P.a / (P.a - P.c) < P.kappa) :
    0 < deltaLow P ∧ deltaLow P < P.a - P.c := by
  obtain ⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩ := hbase
  have hac : 0 < P.a - P.c := by linarith
  have ha : 0 < P.a := by linarith
  have hk0 : 0 < P.kappa := lt_of_le_of_lt (div_nonneg (by positivity) hac.le) hk
  rw [deltaLow_eq P hb1 hb0 hk0 hl0 hl1 hr0 hr1]
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hf3 := fC_le P hb1 hb0
  have r1 : 0 < 1 - P.rho := by linarith
  have hlam2 : 0 < (1 - P.lam) ^ 2 := by have : 0 < 1 - P.lam := by linarith
                                         positivity
  have hlam3 : 0 < P.lam ^ 2 := by positivity
  have hthH : 0 < P.thH := by linarith
  have hR0 : 0 < R0 P := by unfold R0; positivity
  have hS00 : 0 < S00 P := by unfold S00; positivity
  have hS20 : 0 < S20 P := by unfold S20; positivity
  have hAe : 0 < Ae P := by
    unfold Ae
    apply div_pos _ (by linarith)
    linarith [mul_nonneg hb0 hc]
  have hAa : Ae P ≤ P.a := by
    unfold Ae
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_nonneg (sub_nonneg.2 hb1) (add_nonneg ha.le hc)]
  have s00 : S00 P ≤ R0 P := by
    unfold S00 R0
    linarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (by linarith : 0 ≤ 1 - P.thL),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (by linarith : 0 ≤ 1 - P.thH)]
  have s20 : S20 P ≤ S00 P := by
    unfold S20 S00
    have h1 : P.thL ^ 2 ≤ P.thL := by nlinarith only [hL, hLH, hH1]
    have h2 : P.thH ^ 2 ≤ P.thH := by nlinarith only [hL, hLH, hH1]
    linarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (sub_nonneg.2 h2)]
  constructor
  · apply div_pos _ (by positivity)
    positivity
  · rw [div_lt_iff₀ (by positivity)]
    have hk' : P.gamma ^ 2 * P.a < P.kappa * (P.a - P.c) := by
      rwa [div_lt_iff₀ hac] at hk
    have b1 : eC P * S00 P + fC P * S20 P ≤ R0 P := by
      have q1 := mul_le_mul he s00 hS00.le (by norm_num)
      have q2 := mul_le_mul hf3 (s20.trans s00) hS20.le (by norm_num)
      linarith
    have b2 : Ae P * (eC P * S00 P + fC P * S20 P) ≤ P.a * R0 P := by
      apply mul_le_mul hAa b1 (by positivity) (by linarith)
    have hg2 : 0 < P.gamma ^ 2 := by positivity
    have b3 := mul_le_mul_of_nonneg_left b2 hg2.le
    have b4 : P.gamma ^ 2 * P.a * R0 P < P.kappa * (P.a - P.c) * R0 P := mul_lt_mul_of_pos_right hk' hR0
    linarith

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

def UU (P : Params) (Ko Kt : Sig → Sig → ℝ) (w : Outcome) : ℝ :=
  Ae P - eC P * ind w.attack1 * (P.delta - P.gamma * Ko w.y1 w.y2) +
    fC P * ind w.attack2 * (P.delta - P.gamma * Kt w.y2 w.y1)

def Inter (P : Params) (K : Sig → Sig → ℝ) : Prop :=
  ∀ y y', 0 ≤ K y y' ∧ P.gamma * K y y' ≤ P.delta

lemma payoff1_int (P : Params) (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (K1 K2 : Sig → Sig → ℝ)
    (h1 : Inter P K1) (h2 : Inter P K2) (w : Outcome) :
    payoff1 P K1 K2 w = UU P K1 K2 w ^ 2 - P.kappa * K1 w.y1 w.y2 ^ 2 := by
  rw [payoff1_eq P hb hb0, dd_ind P, dd_ind P]
  rw [max_eq_left (by linarith [(h1 w.y1 w.y2).2]), max_eq_left (by linarith [(h2 w.y2 w.y1).2])]
  unfold UU; ring

lemma br_cell (P : Params) (o : Dec) (B : Sig → Sig → ℝ) (y y' : Sig) {w : Outcome}
    (hw : w ∈ cell1 o y y') : br P o w.y1 w.y2 B = br P o y y' B := by
  obtain ⟨h1, h2⟩ := mem_cell hw
  rcases h2 with h2 | h2
  · subst h2
    have := br_adapted P B rfl y w.y2 y'
    rw [h1]; exact this
  · rw [h1, h2]

lemma Ko_cell (P : Params) (o : Dec) (Ko B : Sig → Sig → ℝ)
    (hbr : ∀ y y', Ko y y' = br P o y y' B) (y y' : Sig) {w : Outcome}
    (hw : w ∈ cell1 o y y') : Ko w.y1 w.y2 = Ko y y' := by
  rw [hbr, hbr, br_cell P o B y y' hw]

/-- First-order condition, in cell form. -/
lemma foc2 {P : Params} (h : Hy P) (o : Dec) (Ko Kt : Sig → Sig → ℝ) (hKt : Inter P Kt)
    (hbr : ∀ y y', Ko y y' = br P o y y' Kt) (y y' : Sig) :
    P.kappa * Ko y y' * Pcc P o y y' =
      eC P * P.gamma * ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 * UU P Ko Kt w) := by
  have hC := Cq_pos h o y y'
  have hterm : ∀ w ∈ cell1 o y y', prob P w * (ind w.attack1 * UU P Ko Kt w) =
      prob P w * (ind w.attack1 * uu P Kt w) -
        eC P * (P.delta - P.gamma * Ko y y') * (prob P w * ind w.attack1) := by
    intro w hw
    unfold UU uu
    rw [Ko_cell P o Ko Kt hbr y y' hw]
    rw [dd_ind P, max_eq_left (by linarith [(hKt w.y2 w.y1).2])]
    have := ind_sq w.attack1
    linear_combination (-(prob P w) * eC P * (P.delta - P.gamma * Ko y y')) * this
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change P.kappa * Ko y y' * Pcc P o y y' =
    eC P * P.gamma * (S1c P o y y' Kt - eC P * (P.delta - P.gamma * Ko y y') * S0c P o y y')
  have hb := hbr y y'
  unfold br at hb
  rw [hb]
  field_simp
  ring

/-- Orthogonality of an adapted function against cellwise-null terms. -/
lemma part_S (F : Outcome → ℝ) :
    ∑ w : Outcome, F w = ∑ y : Sig, ∑ y' : Sig, ∑ w ∈ cell1 .S y y', F w := by
  simp only [cell1, Finset.sum_filter]
  rw [sum_outcome]
  simp only [sum_outcome (fun w => if _ then F w else 0)]
  simp [sum_sig]
  ring

lemma part_N (F : Outcome → ℝ) :
    ∑ w : Outcome, F w = ∑ y : Sig, ∑ w ∈ cell1 .N y .L, F w := by
  simp only [cell1, Finset.sum_filter]
  rw [sum_outcome]
  simp only [sum_outcome (fun w => if _ then F w else 0)]
  simp [sum_sig]
  ring

lemma orth (o : Dec) (φ : Sig → Sig → ℝ) (hφ : Adapted o φ) (G : Outcome → ℝ)
    (hG : ∀ y y', ∑ w ∈ cell1 o y y', G w = 0) :
    ∑ w : Outcome, φ w.y1 w.y2 * G w = 0 := by
  cases o
  · rw [part_S]
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro y' _
    have : ∀ w ∈ cell1 .S y y', φ w.y1 w.y2 * G w = φ y y' * G w := by
      intro w hw
      obtain ⟨h1, h2⟩ := mem_cell hw
      rcases h2 with h2 | h2
      · exact absurd h2 (by decide)
      · rw [h1, h2]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hG, mul_zero]
  · rw [part_N]
    apply Finset.sum_eq_zero; intro y _
    have : ∀ w ∈ cell1 .N y .L, φ w.y1 w.y2 * G w = φ y .L * G w := by
      intro w hw
      obtain ⟨h1, -⟩ := mem_cell hw
      rw [h1, hφ rfl y w.y2 .L]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hG, mul_zero]

lemma sum_prob (P : Params) : ∑ w : Outcome, prob P w = 1 := by
  rw [sum_outcome]
  simp [sum_sig, prob, prior, signalProb, attackProb, stateValue]
  ring

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

def U0 (P : Params) (w : Outcome) : ℝ :=
  Ae P - eC P * ind w.attack1 * P.delta + fC P * ind w.attack2 * P.delta

def gF (P : Params) (k1 k2 : ℝ) (w : Outcome) : ℝ :=
  (U0 P w + eC P * P.gamma * ind w.attack1 * k1 - fC P * P.gamma * ind w.attack2 * k2) *
    (U0 P w - fC P * P.gamma * ind w.attack2 * k2)

def FF (P : Params) (K1 K2 : Sig → Sig → ℝ) : ℝ :=
  ∑ w : Outcome, prob P w * gF P (K1 w.y1 w.y2) (K2 w.y2 w.y1) w

lemma UU_eq (P : Params) (K1 K2 : Sig → Sig → ℝ) (w : Outcome) :
    UU P K1 K2 w = U0 P w + eC P * P.gamma * ind w.attack1 * K1 w.y1 w.y2 -
      fC P * P.gamma * ind w.attack2 * K2 w.y2 w.y1 := by
  unfold UU U0; ring

lemma exAnte1_eq {P : Params} (h : Hy P) (o : Dec) (K1 K2 : Sig → Sig → ℝ)
    (hK1 : Inter P K1) (hK2 : Inter P K2) (hA : Adapted o K1)
    (hbr : ∀ y y', K1 y y' = br P o y y' K2) :
    exAnte1 P K1 K2 = FF P K1 K2 := by
  have hb1 := h.1.2.2.1
  have hb0 := h.1.2.1
  set G : Outcome → ℝ := fun w => prob P w * (P.kappa * K1 w.y1 w.y2 -
      eC P * P.gamma * (ind w.attack1 * UU P K1 K2 w)) with hGdef
  have hG : ∀ y y', ∑ w ∈ cell1 o y y', G w = 0 := by
    intro y y'
    have hf := foc2 h o K1 K2 hK2 hbr y y'
    have e1 : ∀ w ∈ cell1 o y y', G w = P.kappa * K1 y y' * prob P w -
        eC P * P.gamma * (prob P w * (ind w.attack1 * UU P K1 K2 w)) := by
      intro w hw
      simp only [hGdef]
      rw [Ko_cell P o K1 K2 hbr y y' hw]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold Pcc at hf
    linarith
  have ho := orth o K1 hA G hG
  unfold exAnte1 FF
  have e2 : ∀ w, prob P w * payoff1 P K1 K2 w =
      prob P w * gF P (K1 w.y1 w.y2) (K2 w.y2 w.y1) w - K1 w.y1 w.y2 * G w := by
    intro w
    rw [payoff1_int P hb1 hb0 K1 K2 hK1 hK2 w]
    simp only [hGdef]
    unfold gF
    rw [UU_eq]
    have := ind_sq w.attack1
    have h2 : ind w.attack1 ^ 2 = ind w.attack1 := by rw [sq]; exact this
    ring
  rw [Finset.sum_congr rfl (fun w _ => e2 w), Finset.sum_sub_distrib, ho, sub_zero]

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

def qq (P : Params) : ℝ := Ae P - eC P * P.delta + fC P * P.delta
def Kb (P : Params) : ℝ := P.gamma * qq P / P.kappa
def eps (P : Params) : ℝ := P.gamma ^ 2 / P.kappa

def W (P : Params) (o : Dec) (y y' : Sig) : ℝ :=
  eC P * P.gamma * ((Ae P - eC P * P.delta) * S0c P o y y' + fC P * P.delta * S2c P o y y') /
    (P.kappa * Pcc P o y y')

def Tc (P : Params) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) : ℝ :=
  ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 * ind w.attack2 * B w.y2 w.y1)

section
variable {P : Params}

lemma S1c_int (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (hB : Inter P B) :
    S1c P o y y' B = Ae P * S0c P o y y' + fC P * P.delta * S2c P o y y' -
      fC P * P.gamma * Tc P o y y' B := by
  unfold S1c S0c S2c Tc
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  unfold uu
  rw [dd_ind, max_eq_left (by linarith [(hB w.y2 w.y1).2])]
  ring

lemma Tc_nonneg (h : P.Standing) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (hB : Inter P B) :
    0 ≤ Tc P o y y' B := by
  unfold Tc
  apply Finset.sum_nonneg
  intro w _
  have := prob_nonneg h w
  have := ind_nonneg w.attack1
  have := ind_nonneg w.attack2
  have := (hB w.y2 w.y1).1
  positivity

lemma Tc_le (h : P.Standing) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (M : ℝ)
    (hB : ∀ z z', B z z' ≤ M) :
    Tc P o y y' B ≤ M * S2c P o y y' := by
  unfold Tc S2c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have := prob_nonneg h w
  have := mul_nonneg (ind_nonneg w.attack1) (ind_nonneg w.attack2)
  have := mul_nonneg (prob_nonneg h w) this
  have h5 := mul_le_mul_of_nonneg_left (hB w.y2 w.y1)
    (mul_nonneg (prob_nonneg h w) (mul_nonneg (ind_nonneg w.attack1) (ind_nonneg w.attack2)))
  linarith

lemma eps_pos (h : P.Standing) : 0 < eps P := by
  obtain ⟨⟨hc, hg, -⟩, -, -, -, -, hk⟩ := h
  unfold eps; positivity

lemma qq_pos (h : P.Standing) : 0 < qq P := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have := Ae_ge P hb1 hb0 hc hcd hd
  have := fC_nonneg P hb1 hb0
  have := mul_nonneg (fC_nonneg P hb1 hb0) hd.le
  unfold qq; linarith

lemma Cq_big (h : Hy P) (o : Dec) (y y' : Sig) :
    P.kappa * Pcc P o y y' / 2 ≤ P.kappa * Pcc P o y y' - (eC P) ^ 2 * P.gamma ^ 2 * S0c P o y y' := by
  obtain ⟨hS, hk2, _⟩ := h
  have hS' := hS
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := hS
  obtain ⟨hP, hS0, hle, -⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have : (eC P) ^ 2 ≤ 1 / 4 := by nlinarith only [he, he0]
  have hg2 : 0 < P.gamma ^ 2 := by positivity
  have h1 : (eC P) ^ 2 * P.gamma ^ 2 * S0c P o y y' ≤ 1 / 4 * P.gamma ^ 2 * Pcc P o y y' := by
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hg2.le hS0.le)
    linarith [mul_le_mul_of_nonneg_left hle hg2.le]
  linarith [mul_le_mul_of_nonneg_right hk2.le hP.le, mul_pos hk hP]

lemma br_le (h : Hy P) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (hB : ∀ z z', 0 ≤ B z z') :
    br P o y y' B ≤ Kb P := by
  have hC := Cq_pos h o y y'
  have hCb := Cq_big h o y y'
  have hS' := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨hP, hS0, hle, hS2, -, -⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hq := qq_pos hS'
  have s1u := S1_upper hS' o y y' B hB
  have hnum : S1c P o y y' B - eC P * P.delta * S0c P o y y' ≤ qq P * Pcc P o y y' := by
    have h1 : fC P * P.delta * S2c P o y y' ≤ fC P * P.delta * S0c P o y y' :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hle hq.le
    have h3 : qq P * S0c P o y y' = (Ae P - eC P * P.delta + fC P * P.delta) * S0c P o y y' := rfl
    linarith
  unfold br Kb
  rw [div_le_div_iff₀ hC hk]
  have hg0 : 0 ≤ eC P * P.gamma := by positivity
  have k1 := mul_le_mul_of_nonneg_left hnum hg0
  have k2 : eC P * P.gamma * (qq P * Pcc P o y y') * P.kappa ≤
      P.gamma * qq P * (P.kappa * Pcc P o y y' / 2) := by
    have : 0 ≤ P.gamma * qq P * Pcc P o y y' * P.kappa := by positivity
    nlinarith only [this, he]
  have k3 := mul_le_mul_of_nonneg_left hCb (by positivity : 0 ≤ P.gamma * qq P)
  linarith [mul_le_mul_of_nonneg_right k1 hk.le]

lemma br_lip2 (h : Hy P) (o : Dec) (y y' : Sig) (B B' : Sig → Sig → ℝ) (M : ℝ)
    (hM : ∀ z z', |B z z' - B' z z'| ≤ M) :
    |br P o y y' B - br P o y y' B'| ≤ fC P * eps P * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM .L .L)
  have hC := Cq_pos h o y y'
  have hCb := Cq_big h o y y'
  have hS' := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨hP, hS0, hle, hS2, -, -⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hd1 := S1_diff hS' o y y' B B' M hM
  have hep := eps_pos hS'
  have e1 : br P o y y' B - br P o y y' B' =
      eC P * P.gamma * (S1c P o y y' B - S1c P o y y' B') /
        (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') := by
    unfold br; ring
  rw [e1, abs_div, abs_of_pos hC, div_le_iff₀ hC, abs_mul, abs_of_pos (by positivity : 0 < eC P * P.gamma)]
  have k1 : eC P * P.gamma * |S1c P o y y' B - S1c P o y y' B'| ≤
      eC P * P.gamma * (fC P * P.gamma * M * Pcc P o y y') :=
    mul_le_mul_of_nonneg_left hd1 (by positivity)
  have k2 : fC P * eps P * M * (P.kappa * Pcc P o y y' / 2) =
      fC P * P.gamma ^ 2 * M * Pcc P o y y' / 2 := by
    unfold eps; field_simp
  have k3 := mul_le_mul_of_nonneg_left hCb (by positivity : 0 ≤ fC P * eps P * M)
  have k4 : eC P * P.gamma * (fC P * P.gamma * M * Pcc P o y y') ≤
      fC P * P.gamma ^ 2 * M * Pcc P o y y' / 2 := by
    have : 0 ≤ fC P * P.gamma ^ 2 * M * Pcc P o y y' := by positivity
    nlinarith only [this, he]
  linarith

lemma br_W (h : Hy P) (o : Dec) (y y' : Sig) (B : Sig → Sig → ℝ) (hB : Inter P B)
    (hBK : ∀ z z', B z z' ≤ Kb P) :
    |br P o y y' B - W P o y y'| ≤ eps P * Kb P / 4 := by
  have hC := Cq_pos h o y y'
  have hS' := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨hP, hS0, hle, hS2, -, -⟩ := cell_facts hS' o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hf3 := fC_le P hb1 hb0
  have hq := qq_pos hS'
  have hKb : 0 < Kb P := by unfold Kb; positivity
  have hT0 := Tc_nonneg hS' o y y' B hB
  have hT1 := Tc_le hS' o y y' B (Kb P) hBK
  have hbr0 := (br_pos_any h o y y' B)
  have hbr1 := br_le h o y y' B (fun z z' => (hB z z').1)
  have hS1 := S1c_int o y y' B hB
  -- key identity
  have key : (br P o y y' B - W P o y y') * (P.kappa * Pcc P o y y') =
      br P o y y' B * (eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') -
        eC P * fC P * P.gamma ^ 2 * Tc P o y y' B := by
    have hbrC : br P o y y' B * (P.kappa * Pcc P o y y' - eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') =
        eC P * P.gamma * (S1c P o y y' B - eC P * P.delta * S0c P o y y') := by
      unfold br; field_simp
    have hW : W P o y y' * (P.kappa * Pcc P o y y') =
        eC P * P.gamma * ((Ae P - eC P * P.delta) * S0c P o y y' + fC P * P.delta * S2c P o y y') := by
      unfold W; field_simp
    rw [hS1] at hbrC
    linear_combination hbrC - hW
  have hKP : 0 < P.kappa * Pcc P o y y' := by positivity
  have hX : 0 ≤ br P o y y' B * (eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') := by positivity
  have hX1 : br P o y y' B * (eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') ≤
      Kb P * P.gamma ^ 2 * Pcc P o y y' / 4 := by
    have e2 : eC P ^ 2 ≤ 1 / 4 := by nlinarith only [he, he0]
    have : eC P ^ 2 * P.gamma ^ 2 * S0c P o y y' ≤ P.gamma ^ 2 * Pcc P o y y' / 4 := by
      have g2 : 0 ≤ P.gamma ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right e2 (mul_nonneg g2 hS0.le), mul_le_mul_of_nonneg_left hle g2]
    calc _ ≤ Kb P * (eC P ^ 2 * P.gamma ^ 2 * S0c P o y y') :=
          mul_le_mul_of_nonneg_right hbr1 (by positivity)
      _ ≤ Kb P * (P.gamma ^ 2 * Pcc P o y y' / 4) := mul_le_mul_of_nonneg_left this hKb.le
      _ = _ := by ring
  have hY : 0 ≤ eC P * fC P * P.gamma ^ 2 * Tc P o y y' B := by positivity
  have hY1 : eC P * fC P * P.gamma ^ 2 * Tc P o y y' B ≤ Kb P * P.gamma ^ 2 * Pcc P o y y' / 4 := by
    have ef : eC P * fC P ≤ 1 / 6 := by nlinarith only [he, he0, hf, hf3]
    have t1 : Tc P o y y' B ≤ Kb P * Pcc P o y y' := by
      linarith [mul_le_mul_of_nonneg_left (hS2.trans hle) hKb.le]
    have g2 : 0 ≤ P.gamma ^ 2 := by positivity
    calc _ ≤ (1 / 6) * P.gamma ^ 2 * Tc P o y y' B := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact mul_le_mul_of_nonneg_right ef g2
      _ ≤ (1 / 6) * P.gamma ^ 2 * (Kb P * Pcc P o y y') :=
          mul_le_mul_of_nonneg_left t1 (by positivity)
      _ ≤ Kb P * P.gamma ^ 2 * Pcc P o y y' / 4 := by
          have := mul_nonneg (mul_nonneg g2 hKb.le) hP.le
          linarith
  have habs : |(br P o y y' B - W P o y y') * (P.kappa * Pcc P o y y')| ≤
      Kb P * P.gamma ^ 2 * Pcc P o y y' / 4 := by
    rw [key, abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_pos hKP] at habs
  have e3 : eps P * Kb P * (P.kappa * Pcc P o y y') = Kb P * P.gamma ^ 2 * Pcc P o y y' := by
    unfold eps; field_simp
  have : |br P o y y' B - W P o y y'| * (P.kappa * Pcc P o y y') ≤
      eps P * Kb P / 4 * (P.kappa * Pcc P o y y') := by
    rw [show eps P * Kb P / 4 * (P.kappa * Pcc P o y y') = Kb P * P.gamma ^ 2 * Pcc P o y y' / 4 by
      rw [← e3]; ring]
    exact habs
  exact le_of_mul_le_mul_right this hKP

end

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

def Q1 (P : Params) : ℝ := Ae P - eC P * P.delta + fC P * P.delta * (P.thL + P.thH)
def Q2 (P : Params) : ℝ := Ae P + fC P * P.delta - eC P * P.delta * (P.thL + P.thH)
def DD (P : Params) : ℝ := P.thH - P.thL

def N1 (P : Params) (o : Dec) (y y' : Sig) : ℝ :=
  (Ae P - eC P * P.delta) * S0c P o y y' + fC P * P.delta * S2c P o y y'
def N2 (P : Params) (o : Dec) (y y' : Sig) : ℝ :=
  (Ae P + fC P * P.delta) * S0c P o y y' - eC P * P.delta * S2c P o y y'

def c1 (P : Params) : ℝ := (Ae P - eC P * P.delta) * P.thL + fC P * P.delta * P.thL ^ 2
def c2 (P : Params) : ℝ := (Ae P + fC P * P.delta) * P.thL - eC P * P.delta * P.thL ^ 2

def hH (P : Params) (o : Dec) (y y' : Sig) : ℝ := P.rho * al P o y y' .H

def Vc (P : Params) : ℝ :=
  (∑ y : Sig, ∑ y' : Sig, hH P .S y y' ^ 2 / Pcc P .S y y') -
    ∑ y : Sig, hH P .N y .L ^ 2 / Pcc P .N y .L

lemma cellTerm_eq (P : Params) (o : Dec) (y y' : Sig) (hP : Pcc P o y y' ≠ 0) :
    N1 P o y y' * N2 P o y y' / Pcc P o y y' =
      c1 P * c2 P * Pcc P o y y' + hH P o y y' * DD P * (c1 P * Q2 P + c2 P * Q1 P) +
        (hH P o y y' * DD P) ^ 2 * Q1 P * Q2 P / Pcc P o y y' := by
  have e0 : S0c P o y y' = Pcc P o y y' * P.thL + hH P o y y' * DD P := by
    unfold S0c Pcc hH DD; rw [cell_S0, cell_P]; ring
  have e2 : S2c P o y y' = Pcc P o y y' * P.thL ^ 2 + hH P o y y' * DD P * (P.thL + P.thH) := by
    unfold S2c Pcc hH DD; rw [cell_S2, cell_P]; ring
  unfold N1 N2
  rw [e0, e2]
  field_simp
  unfold c1 c2 Q1 Q2
  ring

lemma W_eq (P : Params) (o : Dec) (y y' : Sig) :
    W P o y y' = eC P * P.gamma / P.kappa * (N1 P o y y' / Pcc P o y y') := by
  unfold W N1; ring

lemma W_N (P : Params) (y y' : Sig) : W P .N y y' = W P .N y .L := by
  unfold W S0c S2c Pcc; rw [cell1_N y y' .L]

lemma cell_N2 (P : Params) (o : Dec) (y y' : Sig) :
    ∑ w ∈ cell1 o y y', prob P w * (ind w.attack1 *
      (Ae P - eC P * ind w.attack2 * P.delta + fC P * ind w.attack1 * P.delta)) = N2 P o y y' := by
  unfold N2 S0c S2c
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have := ind_sq w.attack1
  linear_combination (prob P w * fC P * P.delta) * this

def swE : Outcome ≃ Outcome := ⟨sw, sw, sw_sw, sw_sw⟩

lemma sum_sw (F : Outcome → ℝ) : ∑ w, F w = ∑ w, F (sw w) :=
  (Equiv.sum_comp swE F).symm

lemma lead_S (P : Params) :
    ∑ w : Outcome, prob P w * (ind w.attack1 *
      (Ae P - eC P * ind w.attack2 * P.delta + fC P * ind w.attack1 * P.delta) * W P .S w.y1 w.y2) =
    ∑ y : Sig, ∑ y' : Sig, W P .S y y' * N2 P .S y y' := by
  rw [part_S]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro y' _
  rw [← cell_N2, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w hw
  obtain ⟨h1, h2⟩ := mem_cell hw
  rcases h2 with h2 | h2
  · exact absurd h2 (by decide)
  · rw [h1, h2]; ring

lemma lead_N (P : Params) :
    ∑ w : Outcome, prob P w * (ind w.attack1 *
      (Ae P - eC P * ind w.attack2 * P.delta + fC P * ind w.attack1 * P.delta) * W P .N w.y1 w.y2) =
    ∑ y : Sig, W P .N y .L * N2 P .N y .L := by
  rw [part_N]
  apply Finset.sum_congr rfl; intro y _
  rw [← cell_N2, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w hw
  obtain ⟨h1, -⟩ := mem_cell hw
  rw [h1, W_N P y w.y2]; ring

lemma sumP_S (P : Params) : ∑ y : Sig, ∑ y' : Sig, Pcc P .S y y' = 1 := by
  simp only [sum_sig, Pcc, cell_P, al, signalProb]; simp; ring

lemma sumP_N (P : Params) : ∑ y : Sig, Pcc P .N y .L = 1 := by
  simp only [sum_sig, Pcc, cell_P, al, signalProb]; simp; ring

lemma sumH_S (P : Params) : ∑ y : Sig, ∑ y' : Sig, hH P .S y y' = P.rho := by
  simp only [sum_sig, hH, al, signalProb]; simp; ring

lemma sumH_N (P : Params) : ∑ y : Sig, hH P .N y .L = P.rho := by
  simp only [sum_sig, hH, al, signalProb]; simp; ring

lemma lead_sum (P : Params) (h : P.Standing) :
    ∑ w : Outcome, prob P w * (ind w.attack2 * U0 P w *
      (W P .S w.y2 w.y1 - W P .N w.y2 w.y1)) =
    eC P * P.gamma / P.kappa * (DD P ^ 2 * Q1 P * Q2 P * Vc P) := by
  rw [sum_sw]
  have e1 : ∀ w : Outcome, prob P (sw w) * (ind (sw w).attack2 * U0 P (sw w) *
      (W P .S (sw w).y2 (sw w).y1 - W P .N (sw w).y2 (sw w).y1)) =
      prob P w * (ind w.attack1 *
      (Ae P - eC P * ind w.attack2 * P.delta + fC P * ind w.attack1 * P.delta) * W P .S w.y1 w.y2) -
      prob P w * (ind w.attack1 *
      (Ae P - eC P * ind w.attack2 * P.delta + fC P * ind w.attack1 * P.delta) * W P .N w.y1 w.y2) := by
    intro w
    rw [prob_sw]
    simp only [sw, U0]
    ring
  rw [Finset.sum_congr rfl (fun w _ => e1 w), Finset.sum_sub_distrib, lead_S, lead_N]
  have hPS : ∀ y y', Pcc P .S y y' ≠ 0 := fun y y' => (cell_facts h .S y y').1.ne'
  have hPN : ∀ y, Pcc P .N y .L ≠ 0 := fun y => (cell_facts h .N y .L).1.ne'
  have t : ∀ o y y', Pcc P o y y' ≠ 0 → W P o y y' * N2 P o y y' =
      eC P * P.gamma / P.kappa * (c1 P * c2 P * Pcc P o y y' + hH P o y y' * DD P * (c1 P * Q2 P + c2 P * Q1 P) +
        (hH P o y y' * DD P) ^ 2 * Q1 P * Q2 P / Pcc P o y y') := by
    intro o y y' hp
    rw [← cellTerm_eq P o y y' hp, W_eq]; ring
  simp only [t _ _ _ (hPS _ _), t _ _ _ (hPN _)]
  have sP := sumP_S P
  have sN := sumP_N P
  have hS := sumH_S P
  have hN := sumH_N P
  simp only [sum_sig] at sP sN hS hN ⊢
  unfold Vc
  simp only [sum_sig]
  linear_combination (eC P * P.gamma / P.kappa) * (c1 P * c2 P * (sP - sN) +
    DD P * (c1 P * Q2 P + c2 P * Q1 P) * (hS - hN))

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

lemma cs_id (h1 h2 p1 p2 : ℝ) (hp1 : 0 < p1) (hp2 : 0 < p2) :
    h1 ^ 2 / p1 + h2 ^ 2 / p2 - (h1 + h2) ^ 2 / (p1 + p2) =
      (h1 * p2 - h2 * p1) ^ 2 / (p1 * p2 * (p1 + p2)) := by
  field_simp; ring

lemma Vc_pos (P : Params) (h : P.Standing) : 0 < Vc P := by
  have hP : ∀ y y', 0 < Pcc P .S y y' := fun y y' => (cell_facts h .S y y').1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, -⟩ := h
  have aN : ∀ y, hH P .N y .L = hH P .S y .L + hH P .S y .H := by
    intro y; cases y <;> simp [hH, al, signalProb] <;> ring
  have pN : ∀ y, Pcc P .N y .L = Pcc P .S y .L + Pcc P .S y .H := by
    intro y; cases y <;> simp [Pcc, cell_P, al, signalProb] <;> ring
  have key : Vc P = ∑ y : Sig, (hH P .S y .L * Pcc P .S y .H - hH P .S y .H * Pcc P .S y .L) ^ 2 /
      (Pcc P .S y .L * Pcc P .S y .H * (Pcc P .S y .L + Pcc P .S y .H)) := by
    unfold Vc
    simp only [sum_sig, aN, pN]
    rw [← cs_id _ _ _ _ (hP .L .L) (hP .L .H), ← cs_id _ _ _ _ (hP .H .L) (hP .H .H)]
    ring
  rw [key, sum_sig]
  have t1 : 0 ≤ (hH P .S .L .L * Pcc P .S .L .H - hH P .S .L .H * Pcc P .S .L .L) ^ 2 /
      (Pcc P .S .L .L * Pcc P .S .L .H * (Pcc P .S .L .L + Pcc P .S .L .H)) := by
    have := hP .L .L; have := hP .L .H; positivity
  have hX : hH P .S .H .L * Pcc P .S .H .H - hH P .S .H .H * Pcc P .S .H .L =
      P.rho * P.lam * (1 - P.lam) * (1 - P.rho) * (1 - 2 * P.lam) := by
    simp [hH, Pcc, cell_P, al, signalProb]; ring
  have t2 : 0 < (hH P .S .H .L * Pcc P .S .H .H - hH P .S .H .H * Pcc P .S .H .L) ^ 2 /
      (Pcc P .S .H .L * Pcc P .S .H .H * (Pcc P .S .H .L + Pcc P .S .H .H)) := by
    have := hP .H .L; have := hP .H .H
    rw [hX]
    have : P.rho * P.lam * (1 - P.lam) * (1 - P.rho) * (1 - 2 * P.lam) ≠ 0 := by
      have a1 : 0 < 1 - P.lam := by linarith
      have a2 : 0 < 1 - P.rho := by linarith
      have a3 : 1 - 2 * P.lam < 0 := by linarith
      have : 0 < P.rho * P.lam * (1 - P.lam) * (1 - P.rho) := by
        have : 0 < P.lam := by linarith
        positivity
      exact (mul_neg_of_pos_of_neg this a3).ne
    positivity
  linarith

end CyberShare.Sharing.P2


lemma prod_diff_le (x1 x2 y1 y2 M : ℝ) (hx1 : 0 ≤ x1) (hx1' : x1 ≤ M) (hx2 : 0 ≤ x2) (hx2' : x2 ≤ M)
    (hy1 : 0 ≤ y1) (hy1' : y1 ≤ M) (hy2 : 0 ≤ y2) (hy2' : y2 ≤ M) :
    |x1 * x2 - y1 * y2| ≤ M ^ 2 := by
  have a : x1 * x2 ≤ M ^ 2 := by rw [sq]; exact mul_le_mul hx1' hx2' hx2 (hx1.trans hx1')
  have b : y1 * y2 ≤ M ^ 2 := by rw [sq]; exact mul_le_mul hy1' hy2' hy2 (hy1.trans hy1')
  have c := mul_nonneg hx1 hx2
  have d := mul_nonneg hy1 hy2
  rw [abs_le]; constructor <;> linarith

lemma rem_bound (e f g ε Kb q A U1 U2 i12 i2 k1X k1Y k2X k2Y WX WY : ℝ)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 2) (hf0 : 0 ≤ f) (hf : f ≤ 1 / 3) (hg : 0 < g) (hε : 0 ≤ ε)
    (hKb : 0 ≤ Kb) (hgK : g * Kb = ε * q) (hq : 0 ≤ q) (hqA : q ≤ A)
    (hU1 : 0 ≤ U1) (hU1' : U1 ≤ q) (hU2 : 0 ≤ U2) (hU2' : U2 ≤ A)
    (hi12 : 0 ≤ i12) (hi12' : i12 ≤ 1) (hi2 : 0 ≤ i2) (hi2' : i2 ≤ 1)
    (a1 : 0 ≤ k1X) (a1' : k1X ≤ Kb) (b1 : 0 ≤ k1Y) (b1' : k1Y ≤ Kb)
    (a2 : 0 ≤ k2X) (a2' : k2X ≤ Kb) (b2 : 0 ≤ k2Y) (b2' : k2Y ≤ Kb)
    (h1 : |k1X - k1Y| ≤ f * ε * Kb) (h2 : |k2X - WX| ≤ ε * Kb / 4) (h3 : |k2Y - WY| ≤ ε * Kb / 4) :
    |e * g * U1 * (k1X - k1Y) - 2 * f * g * U2 * ((k2X - WX) - (k2Y - WY)) -
        e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y) + f ^ 2 * g ^ 2 * i2 * (k2X ^ 2 - k2Y ^ 2)| ≤
      3 * f * g * ε * Kb * A := by
  set X := f * g * ε * Kb with hX
  have hX0 : 0 ≤ X := by positivity
  have t1 : |e * g * U1 * (k1X - k1Y)| ≤ q * X / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ e * g * U1)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ e * g * U1)
    have e1 : e * g * U1 * (f * ε * Kb) = e * U1 * X := by rw [hX]; ring
    have e2 : e * U1 * X ≤ q * X / 2 := by
      have h5 := mul_le_mul he hU1' hU1 (by norm_num : (0:ℝ) ≤ 1 / 2)
      have h6 := mul_le_mul_of_nonneg_right h5 hX0
      linarith
    linarith
  have t2 : |2 * f * g * U2 * ((k2X - WX) - (k2Y - WY))| ≤ A * X := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * f * g * U2)]
    have h4 : |(k2X - WX) - (k2Y - WY)| ≤ ε * Kb / 2 := by
      have := abs_sub (k2X - WX) (k2Y - WY); linarith
    have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * f * g * U2)
    have e1 : 2 * f * g * U2 * (ε * Kb / 2) = U2 * X := by rw [hX]; ring
    have h7 := mul_le_mul_of_nonneg_right hU2' hX0
    linarith
  have hP1 := prod_diff_le k1X k2X k1Y k2Y Kb a1 a1' a2 a2' b1 b1' b2 b2'
  have hP2 := prod_diff_le k2X k2X k2Y k2Y Kb a2 a2' a2 a2' b2 b2' b2 b2'
  have hK2 : g ^ 2 * Kb ^ 2 = q * (g * ε * Kb) := by
    linear_combination (g * Kb) * hgK
  have t3 : |e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y)| ≤ q * X / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ e * f * g ^ 2 * i12)]
    have := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ e * f * g ^ 2 * i12)
    have e1 : e * f * g ^ 2 * i12 * Kb ^ 2 = e * i12 * q * X := by
      rw [hX]; linear_combination (e * f * i12) * hK2
    have e2 : e * i12 * q * X ≤ q * X / 2 := by
      have h5 : e * i12 ≤ 1 / 2 * 1 := mul_le_mul he hi12' hi12 (by norm_num)
      have h6 := mul_le_mul_of_nonneg_right h5 (mul_nonneg hq hX0)
      have e7 : e * i12 * q * X = e * i12 * (q * X) := by ring
      rw [e7]; linarith
    linarith
  have t4 : |f ^ 2 * g ^ 2 * i2 * (k2X ^ 2 - k2Y ^ 2)| ≤ q * X / 3 := by
    have hP2' : |k2X ^ 2 - k2Y ^ 2| ≤ Kb ^ 2 := by
      have e0 : k2X ^ 2 - k2Y ^ 2 = k2X * k2X - k2Y * k2Y := by ring
      rw [e0]; exact hP2
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ f ^ 2 * g ^ 2 * i2)]
    have := mul_le_mul_of_nonneg_left hP2' (by positivity : 0 ≤ f ^ 2 * g ^ 2 * i2)
    have e1 : f ^ 2 * g ^ 2 * i2 * Kb ^ 2 = f * i2 * q * X := by
      rw [hX]; linear_combination (f ^ 2 * i2) * hK2
    have e2 : f * i2 * q * X ≤ q * X / 3 := by
      have h5 : f * i2 ≤ 1 / 3 * 1 := mul_le_mul hf hi2' hi2 (by norm_num)
      have h6 := mul_le_mul_of_nonneg_right h5 (mul_nonneg hq hX0)
      have e7 : f * i2 * q * X = f * i2 * (q * X) := by ring
      rw [e7]; linarith
    linarith
  have tri : |e * g * U1 * (k1X - k1Y) - 2 * f * g * U2 * ((k2X - WX) - (k2Y - WY)) -
        e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y) + f ^ 2 * g ^ 2 * i2 * (k2X ^ 2 - k2Y ^ 2)| ≤
      |e * g * U1 * (k1X - k1Y)| + |2 * f * g * U2 * ((k2X - WX) - (k2Y - WY))| +
        |e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y)| + |f ^ 2 * g ^ 2 * i2 * (k2X ^ 2 - k2Y ^ 2)| := by
    have s1 := abs_add_le (e * g * U1 * (k1X - k1Y) - 2 * f * g * U2 * ((k2X - WX) - (k2Y - WY)) -
        e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y)) (f ^ 2 * g ^ 2 * i2 * (k2X ^ 2 - k2Y ^ 2))
    have s2 := abs_sub (e * g * U1 * (k1X - k1Y) - 2 * f * g * U2 * ((k2X - WX) - (k2Y - WY)))
        (e * f * g ^ 2 * i12 * (k1X * k2X - k1Y * k2Y))
    have s3 := abs_sub (e * g * U1 * (k1X - k1Y)) (2 * f * g * U2 * ((k2X - WX) - (k2Y - WY)))
    linarith
  have fin : q * X / 2 + A * X + q * X / 2 + q * X / 3 ≤ 3 * f * g * ε * Kb * A := by
    have : 3 * f * g * ε * Kb * A = 3 * A * X := by rw [hX]; ring
    rw [this]
    have h7 := mul_le_mul_of_nonneg_right hqA hX0
    have h8 : 0 ≤ A * X := mul_nonneg (hq.trans hqA) hX0
    linarith
  linarith


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

lemma eq_facts {P : Params} (h : Hy P) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ)
    (hE : IsInvEq P s1 s2 K1 K2) :
    Inter P K1 ∧ Inter P K2 ∧ (∀ y y', K1 y y' ≤ Kb P) ∧ (∀ y y', K2 y y' ≤ Kb P) ∧
      Adapted s2 K1 ∧ (∀ y y', K1 y y' = br P s2 y y' K2) ∧ (∀ y y', K2 y y' = br P s1 y y' K1) := by
  rw [invEq_iff h] at hE
  obtain ⟨a1, a2, n, b1, b2⟩ := hE
  have n1 : ∀ z z', 0 ≤ K1 z z' := fun z z' => (n z z').1
  have n2 : ∀ z z', 0 ≤ K2 z z' := fun z z' => (n z z').2
  refine ⟨?_, ?_, ?_, ?_, a1, b1, b2⟩
  · intro y y'
    refine ⟨n1 y y', ?_⟩
    rw [b1]; exact (br_bounds h s2 y y' K2 n2).2.2.le
  · intro y y'
    refine ⟨n2 y y', ?_⟩
    rw [b2]; exact (br_bounds h s1 y y' K1 n1).2.2.le
  · intro y y'; rw [b1]; exact br_le h s2 y y' K2 n2
  · intro y y'; rw [b2]; exact br_le h s1 y y' K1 n1

lemma pt_id (P : Params) (k1X k2X k1Y k2Y WX WY : ℝ) (w : Outcome) :
    gF P k1X k2X w - gF P k1Y k2Y w +
        2 * fC P * P.gamma * (ind w.attack2 * U0 P w * (WX - WY)) =
      eC P * P.gamma * (ind w.attack1 * U0 P w) * (k1X - k1Y) -
        2 * fC P * P.gamma * (ind w.attack2 * U0 P w) * ((k2X - WX) - (k2Y - WY)) -
        eC P * fC P * P.gamma ^ 2 * (ind w.attack1 * ind w.attack2) * (k1X * k2X - k1Y * k2Y) +
        fC P ^ 2 * P.gamma ^ 2 * ind w.attack2 * (k2X ^ 2 - k2Y ^ 2) := by
  unfold gF
  have := ind_sq w.attack2
  linear_combination (fC P ^ 2 * P.gamma ^ 2 * (k2X ^ 2 - k2Y ^ 2)) * this

lemma U_bounds {P : Params} (h : P.Standing) (w : Outcome) :
    0 ≤ ind w.attack1 * U0 P w ∧ ind w.attack1 * U0 P w ≤ qq P ∧
    0 ≤ ind w.attack2 * U0 P w ∧ ind w.attack2 * U0 P w ≤ Ae P + fC P * P.delta := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hA := Ae_ge P hb1 hb0 hc hcd hd
  have hf := fC_nonneg P hb1 hb0
  have he := eC_pos P hb1 hb0
  have h1 : 0 ≤ fC P * P.delta := by positivity
  have h2 : 0 ≤ eC P * P.delta := by positivity
  unfold U0 qq
  cases w.attack1 <;> cases w.attack2 <;>
    simp only [ind, if_true, if_false, Bool.false_eq_true, one_mul, zero_mul, mul_one, mul_zero] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma delta_est {P : Params} (h : Hy P) (o : Dec) (K1X K2X K1Y K2Y : Sig → Sig → ℝ)
    (hX : IsInvEq P .S o K1X K2X) (hY : IsInvEq P .N o K1Y K2Y) :
    |exAnte1 P K1X K2X - exAnte1 P K1Y K2Y +
        2 * fC P * eps P * eC P * (DD P ^ 2 * Q1 P * Q2 P * Vc P)| ≤
      3 * fC P * P.gamma * eps P * Kb P * (Ae P + fC P * P.delta) := by
  have hS := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  obtain ⟨iX1, iX2, kX1, kX2, aX, bX1, bX2⟩ := eq_facts h .S o K1X K2X hX
  obtain ⟨iY1, iY2, kY1, kY2, aY, bY1, bY2⟩ := eq_facts h .N o K1Y K2Y hY
  rw [exAnte1_eq h o K1X K2X iX1 iX2 aX bX1, exAnte1_eq h o K1Y K2Y iY1 iY2 aY bY1]
  have hlead := lead_sum P hS
  have hlead2 : 2 * fC P * eps P * eC P * (DD P ^ 2 * Q1 P * Q2 P * Vc P) =
      ∑ w : Outcome, prob P w * (2 * fC P * P.gamma * (ind w.attack2 * U0 P w *
        (W P .S w.y2 w.y1 - W P .N w.y2 w.y1))) := by
    have : ∀ w : Outcome, prob P w * (2 * fC P * P.gamma * (ind w.attack2 * U0 P w *
        (W P .S w.y2 w.y1 - W P .N w.y2 w.y1))) = (2 * fC P * P.gamma) *
        (prob P w * (ind w.attack2 * U0 P w * (W P .S w.y2 w.y1 - W P .N w.y2 w.y1))) := by
      intro w; ring
    rw [Finset.sum_congr rfl (fun w _ => this w), ← Finset.mul_sum, hlead]
    unfold eps; field_simp
  rw [hlead2]
  unfold FF
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hKb0 : 0 ≤ Kb P := by unfold Kb; have := qq_pos hS; positivity
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hf3 := fC_le P hb1 hb0
  have hq := qq_pos hS
  have hep := eps_pos hS
  have hqA : qq P ≤ Ae P + fC P * P.delta := by
    have := mul_pos he0 hd; unfold qq; linarith
  have hgK : P.gamma * Kb P = eps P * qq P := by unfold Kb eps; field_simp
  -- differences
  have dK1 : ∀ y y', |K1X y y' - K1Y y y'| ≤ fC P * eps P * Kb P := by
    intro y y'
    rw [bX1, bY1]
    apply br_lip2 h o y y' K2X K2Y (Kb P)
    intro z z'
    rw [abs_le]; constructor <;> linarith [kX2 z z', kY2 z z', (iX2 z z').1, (iY2 z z').1]
  have dX2 : ∀ y y', |K2X y y' - W P .S y y'| ≤ eps P * Kb P / 4 := by
    intro y y'; rw [bX2]; exact br_W h .S y y' K1X iX1 kX1
  have dY2 : ∀ y y', |K2Y y y' - W P .N y y'| ≤ eps P * Kb P / 4 := by
    intro y y'; rw [bY2]; exact br_W h .N y y' K1Y iY1 kY1
  have pt : ∀ w : Outcome, |prob P w * gF P (K1X w.y1 w.y2) (K2X w.y2 w.y1) w -
      prob P w * gF P (K1Y w.y1 w.y2) (K2Y w.y2 w.y1) w +
      prob P w * (2 * fC P * P.gamma * (ind w.attack2 * U0 P w *
        (W P .S w.y2 w.y1 - W P .N w.y2 w.y1)))| ≤
      prob P w * (3 * fC P * P.gamma * eps P * Kb P * (Ae P + fC P * P.delta)) := by
    intro w
    have hp := prob_nonneg hS w
    have e1 : prob P w * gF P (K1X w.y1 w.y2) (K2X w.y2 w.y1) w -
      prob P w * gF P (K1Y w.y1 w.y2) (K2Y w.y2 w.y1) w +
      prob P w * (2 * fC P * P.gamma * (ind w.attack2 * U0 P w *
        (W P .S w.y2 w.y1 - W P .N w.y2 w.y1))) =
      prob P w * (gF P (K1X w.y1 w.y2) (K2X w.y2 w.y1) w - gF P (K1Y w.y1 w.y2) (K2Y w.y2 w.y1) w +
        2 * fC P * P.gamma * (ind w.attack2 * U0 P w * (W P .S w.y2 w.y1 - W P .N w.y2 w.y1))) := by
      ring
    rw [e1, pt_id, abs_mul, abs_of_nonneg hp]
    apply mul_le_mul_of_nonneg_left _ hp
    obtain ⟨u1, u1', u2, u2'⟩ := U_bounds hS w
    exact rem_bound (eC P) (fC P) P.gamma (eps P) (Kb P) (qq P) (Ae P + fC P * P.delta)
      _ _ _ _ _ _ _ _ _ _ he0.le he hf hf3 hg hep.le hKb0 hgK hq.le hqA u1 u1' u2 u2'
      (mul_nonneg (ind_nonneg _) (ind_nonneg _))
      (mul_le_one₀ (ind_le _) (ind_nonneg _) (ind_le _))
      (ind_nonneg _) (ind_le _)
      (iX1 _ _).1 (kX1 _ _) (iY1 _ _).1 (kY1 _ _) (iX2 _ _).1 (kX2 _ _) (iY2 _ _).1 (kY2 _ _)
      (dK1 _ _) (dX2 _ _) (dY2 _ _)
  calc _ ≤ ∑ w : Outcome, |prob P w * gF P (K1X w.y1 w.y2) (K2X w.y2 w.y1) w -
      prob P w * gF P (K1Y w.y1 w.y2) (K2Y w.y2 w.y1) w +
      prob P w * (2 * fC P * P.gamma * (ind w.attack2 * U0 P w *
        (W P .S w.y2 w.y1 - W P .N w.y2 w.y1)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : Outcome, prob P w * (3 * fC P * P.gamma * eps P * Kb P * (Ae P + fC P * P.delta)) :=
        Finset.sum_le_sum (fun w _ => pt w)
    _ = _ := by rw [← Finset.sum_mul, sum_prob, one_mul]

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

lemma eC_ge (P : Params) (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) : 1 / 3 ≤ eC P := by
  unfold eC
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

lemma Q1_ge {P : Params} (h : P.Standing) : qq P ≤ Q1 P := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hf := fC_nonneg P hb1 hb0
  unfold qq Q1
  have : 0 ≤ fC P * P.delta * (P.thL + P.thH - 1) := by
    apply mul_nonneg (by positivity); linarith
  linarith

lemma gap_neg {P : Params} (h : Hy P) (hb : 0 < P.b) (o : Dec) (m : ℝ) (hm : 0 < m)
    (hQ : m ≤ Q2 P) (hε : 9 * eps P * (Ae P + fC P * P.delta) < 2 * DD P ^ 2 * m * Vc P)
    (K1X K2X K1Y K2Y : Sig → Sig → ℝ)
    (hX : IsInvEq P .S o K1X K2X) (hY : IsInvEq P .N o K1Y K2Y) :
    exAnte1 P K1X K2X < exAnte1 P K1Y K2Y := by
  have hS := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  have est := delta_est h o K1X K2X K1Y K2Y hX hY
  have hgK : P.gamma * Kb P = eps P * qq P := by unfold Kb eps; field_simp
  have hf : 0 < fC P := by unfold fC; apply div_pos hb; nlinarith only [hb1, hb]
  have he3 := eC_ge P hb1 hb0
  have hq := qq_pos hS
  have hQ1 := Q1_ge hS
  have hep := eps_pos hS
  have hV := Vc_pos P hS
  have hD2 : 0 ≤ DD P ^ 2 := sq_nonneg _
  set Z := fC P * eps P * qq P with hZ
  have hZ0 : 0 < Z := by positivity
  have r1 : 3 * fC P * P.gamma * eps P * Kb P * (Ae P + fC P * P.delta) =
      3 * Z * (eps P * (Ae P + fC P * P.delta)) := by
    rw [hZ]; linear_combination (3 * fC P * eps P * (Ae P + fC P * P.delta)) * hgK
  have r2 : 3 * Z * (eps P * (Ae P + fC P * P.delta)) < Z * ((2 / 3) * DD P ^ 2 * m * Vc P) := by
    have := mul_lt_mul_of_pos_left hε hZ0
    linarith
  have l1 : (1 / 3) * qq P * m ≤ eC P * Q1 P * Q2 P := by
    have a1 : (1 / 3) * qq P ≤ eC P * Q1 P := mul_le_mul he3 hQ1 hq.le (by linarith)
    exact mul_le_mul a1 hQ (by linarith) (by linarith)
  have l2 : Z * ((2 / 3) * DD P ^ 2 * m * Vc P) ≤
      2 * fC P * eps P * eC P * (DD P ^ 2 * Q1 P * Q2 P * Vc P) := by
    have := mul_le_mul_of_nonneg_left l1 (by positivity : 0 ≤ 2 * fC P * eps P * DD P ^ 2 * Vc P)
    rw [hZ]; linarith
  rw [abs_le] at est
  linarith [est.2]

lemma gap_pos {P : Params} (h : Hy P) (hb : 0 < P.b) (o : Dec) (m : ℝ) (hm : 0 < m)
    (hQ : Q2 P ≤ -m) (hε : 9 * eps P * (Ae P + fC P * P.delta) < 2 * DD P ^ 2 * m * Vc P)
    (K1X K2X K1Y K2Y : Sig → Sig → ℝ)
    (hX : IsInvEq P .S o K1X K2X) (hY : IsInvEq P .N o K1Y K2Y) :
    exAnte1 P K1Y K2Y < exAnte1 P K1X K2X := by
  have hS := h.1
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h.1
  have est := delta_est h o K1X K2X K1Y K2Y hX hY
  have hgK : P.gamma * Kb P = eps P * qq P := by unfold Kb eps; field_simp
  have hf : 0 < fC P := by unfold fC; apply div_pos hb; nlinarith only [hb1, hb]
  have he3 := eC_ge P hb1 hb0
  have hq := qq_pos hS
  have hQ1 := Q1_ge hS
  have hep := eps_pos hS
  have hV := Vc_pos P hS
  set Z := fC P * eps P * qq P with hZ
  have hZ0 : 0 < Z := by positivity
  have r1 : 3 * fC P * P.gamma * eps P * Kb P * (Ae P + fC P * P.delta) =
      3 * Z * (eps P * (Ae P + fC P * P.delta)) := by
    rw [hZ]; linear_combination (3 * fC P * eps P * (Ae P + fC P * P.delta)) * hgK
  have r2 : 3 * Z * (eps P * (Ae P + fC P * P.delta)) < Z * ((2 / 3) * DD P ^ 2 * m * Vc P) := by
    have := mul_lt_mul_of_pos_left hε hZ0
    linarith
  have l1 : (1 / 3) * qq P * m ≤ eC P * Q1 P * (-Q2 P) := by
    have a1 : (1 / 3) * qq P ≤ eC P * Q1 P := mul_le_mul he3 hQ1 hq.le (by linarith)
    exact mul_le_mul a1 (by linarith) (by linarith) (by linarith)
  have l2 : Z * ((2 / 3) * DD P ^ 2 * m * Vc P) ≤
      -(2 * fC P * eps P * eC P * (DD P ^ 2 * Q1 P * Q2 P * Vc P)) := by
    have := mul_le_mul_of_nonneg_left l1 (by positivity : 0 ≤ 2 * fC P * eps P * DD P ^ 2 * Vc P)
    rw [hZ]; linarith
  rw [abs_le] at est
  linarith [est.1]

/-! ## Symmetry -/

lemma exAnte2_eq (P : Params) (K1 K2 : Sig → Sig → ℝ) : exAnte2 P K1 K2 = exAnte1 P K2 K1 := by
  unfold exAnte2 exAnte1
  rw [sum_sw]
  apply Finset.sum_congr rfl
  intro w _
  rw [prob_sw, payoff2_sw]

lemma invEq_symm (P : Params) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ) :
    IsInvEq P s1 s2 K1 K2 ↔ IsInvEq P s2 s1 K2 K1 := by
  rw [invEq_iff_best, invEq_iff_best]
  constructor
  · rintro ⟨a, b, c, d, e⟩; exact ⟨b, a, fun y y' => ⟨(c y y').2, (c y y').1⟩, e, d⟩
  · rintro ⟨a, b, c, d, e⟩; exact ⟨b, a, fun y y' => ⟨(c y y').2, (c y y').1⟩, e, d⟩

lemma exInv {P : Params} (h : Hy P) (s1 s2 : Dec) : ∃ K1 K2, IsInvEq P s1 s2 K1 K2 := by
  obtain ⟨p, hp, -⟩ := exists_unique_inv h s1 s2
  exact ⟨p.1, p.2, hp⟩

lemma share_unique {P : Params} (h : Hy P)
    (hpos : ∀ o : Dec, ∀ K1X K2X K1Y K2Y : Sig → Sig → ℝ,
      IsInvEq P .S o K1X K2X → IsInvEq P .N o K1Y K2Y → exAnte1 P K1Y K2Y < exAnte1 P K1X K2X) :
    IsSharingEq P .S .S ∧ ∀ s1 s2 : Dec, IsSharingEq P s1 s2 → s1 = .S ∧ s2 = .S := by
  refine ⟨⟨exInv h _ _, exInv h _ _, exInv h _ _, ?_, ?_⟩, ?_⟩
  · intro K1 K2 K1' K2' hE hE'
    exact (hpos .S K1 K2 K1' K2' hE hE').le
  · intro K1 K2 K1' K2' hE hE'
    rw [exAnte2_eq, exAnte2_eq]
    rw [invEq_symm] at hE hE'
    exact (hpos .S K2 K1 K2' K1' hE hE').le
  · intro s1 s2 hSE
    obtain ⟨⟨K1, K2, hE⟩, ⟨K1', K2', hE'⟩, ⟨K1'', K2'', hE''⟩, c1, c2⟩ := hSE
    cases s1 <;> cases s2
    · exact ⟨rfl, rfl⟩
    · -- (S, N): firm 2 deviates to S
      exfalso
      have := c2 K1 K2 K1'' K2'' hE hE''
      rw [exAnte2_eq, exAnte2_eq] at this
      rw [invEq_symm] at hE hE''
      have := hpos .S K2'' K1'' K2 K1 hE'' hE
      linarith
    · -- (N, S)
      exfalso
      have := c1 K1 K2 K1' K2' hE hE'
      have := hpos .S K1' K2' K1 K2 hE' hE
      linarith
    · -- (N, N)
      exfalso
      have := c1 K1 K2 K1' K2' hE hE'
      have := hpos .N K1' K2' K1 K2 hE' hE
      linarith

lemma nonshare_unique {P : Params} (h : Hy P)
    (hneg : ∀ o : Dec, ∀ K1X K2X K1Y K2Y : Sig → Sig → ℝ,
      IsInvEq P .S o K1X K2X → IsInvEq P .N o K1Y K2Y → exAnte1 P K1X K2X < exAnte1 P K1Y K2Y) :
    IsSharingEq P .N .N ∧ ∀ s1 s2 : Dec, IsSharingEq P s1 s2 → s1 = .N ∧ s2 = .N := by
  refine ⟨⟨exInv h _ _, exInv h _ _, exInv h _ _, ?_, ?_⟩, ?_⟩
  · intro K1 K2 K1' K2' hE hE'
    exact (hneg .N K1' K2' K1 K2 hE' hE).le
  · intro K1 K2 K1' K2' hE hE'
    rw [exAnte2_eq, exAnte2_eq]
    rw [invEq_symm] at hE hE'
    exact (hneg .N K2' K1' K2 K1 hE' hE).le
  · intro s1 s2 hSE
    obtain ⟨⟨K1, K2, hE⟩, ⟨K1', K2', hE'⟩, ⟨K1'', K2'', hE''⟩, c1, c2⟩ := hSE
    cases s1 <;> cases s2
    · exfalso
      have := c1 K1 K2 K1' K2' hE hE'
      have := hneg .S K1 K2 K1' K2' hE hE'
      linarith
    · -- (S, N)
      exfalso
      have := c1 K1 K2 K1' K2' hE hE'
      have := hneg .N K1 K2 K1' K2' hE hE'
      linarith
    · -- (N, S): firm 2 deviates to N
      exfalso
      have := c2 K1 K2 K1'' K2'' hE hE''
      rw [exAnte2_eq, exAnte2_eq] at this
      rw [invEq_symm] at hE hE''
      have := hneg .N K2 K1 K2'' K1'' hE hE''
      linarith
    · exact ⟨rfl, rfl⟩

end CyberShare.Sharing.P2


open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.P2

section
variable (P : Params)

lemma Ae_lo (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hc : 0 ≤ P.c) (ha : 0 ≤ P.a) :
    (P.a - P.c) / 2 ≤ Ae P := by
  unfold Ae; rw [le_div_iff₀ (by linarith)]; linarith [mul_nonneg hb0 hc, mul_nonneg hb0 ha]

lemma Ae_hi (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hc : 0 ≤ P.c) (ha : 0 ≤ P.a) :
    Ae P ≤ (P.a - P.c) / 2 + P.b * (P.a + P.c) / 2 := by
  unfold Ae; rw [div_le_iff₀ (by linarith)]
  linarith [mul_nonneg (mul_nonneg hb0 hb0) hc, mul_nonneg (mul_nonneg hb0 hb0) ha,
    mul_nonneg hb0 hc, mul_nonneg hb0 ha, mul_nonneg (mul_nonneg hb0 (sub_nonneg.2 hb1)) (add_nonneg ha hc)]

lemma Ae_le_a (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hc : 0 ≤ P.c) (ha : 0 ≤ P.a) :
    Ae P ≤ P.a := by
  unfold Ae; rw [div_le_iff₀ (by linarith)]
  linarith [mul_nonneg (sub_nonneg.2 hb1) hc, mul_nonneg (sub_nonneg.2 hb1) ha]

lemma Ae_H (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hc : 0 ≤ P.c) (ha : 0 ≤ P.a) :
    P.a - (1 - P.b) * (P.a + P.c) ≤ Ae P := by
  unfold Ae; rw [le_div_iff₀ (by linarith)]
  linarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hb1)) (add_nonneg ha hc)]

lemma eC_lo (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) : 1 / 2 - P.b / 6 ≤ eC P := by
  unfold eC; rw [le_div_iff₀ (by nlinarith)]
  linarith [mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1)]

lemma eC_H (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) : eC P ≤ 1 / 3 + (1 - P.b) := by
  unfold eC; rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1)]

lemma fC_hi (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) : fC P ≤ P.b / 3 := by
  unfold fC; rw [div_le_iff₀ (by nlinarith)]
  linarith [mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1)]

lemma fC_H (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) : 1 / 3 - (1 - P.b) ≤ fC P := by
  unfold fC; rw [le_div_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1)]

end

lemma Q2_small {P : Params} (h : P.Standing) (hδ : P.delta ≤ (P.a - P.c) / 4) :
    (P.a - P.c) / 4 ≤ Q2 P := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have hA := Ae_lo P hb0 hb1 hc (by linarith)
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hs : P.thL + P.thH ≤ 2 := by linarith
  have h1 : eC P * P.delta * (P.thL + P.thH) ≤ (1 / 2) * P.delta * 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right he hd.le) hs (by linarith) (by positivity)
  unfold Q2
  linarith [mul_nonneg hf hd.le]

lemma Q2_H {P : Params} (h : P.Standing) (hb : 14 / 15 ≤ P.b) :
    P.a / 3 ≤ Q2 P := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have ha : 0 ≤ P.a := by linarith
  have hA := Ae_H P hb0 hb1 hc ha
  have he := eC_H P hb0 hb1
  have hf := fC_H P hb0 hb1
  set β := 1 - P.b with hβ
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β ≤ 1 / 15 := by linarith
  set s := P.thL + P.thH with hs
  have hs2 : s ≤ 2 := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hδa : P.delta ≤ P.a := by linarith
  -- Q2 ≥ Ae + (1/3 - β) δ - (1/3 + β) δ s
  have k1 : (1 / 3 - β) * P.delta ≤ fC P * P.delta := mul_le_mul_of_nonneg_right hf hd.le
  have k2 : eC P * P.delta * s ≤ (1 / 3 + β) * P.delta * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hd.le) (by linarith)
  have k3 : P.delta * (s - 1) ≤ P.a * 1 := mul_le_mul hδa (by linarith) (by linarith) ha
  have k4 : β * P.delta * (1 + s) ≤ (1 / 15) * P.a * 3 :=
    mul_le_mul (mul_le_mul hβ1 hδa hd.le (by norm_num)) (by linarith) (by linarith) (by positivity)
  have k5 : β * (P.a + P.c) ≤ (1 / 15) * (2 * P.a) := mul_le_mul hβ1 (by linarith) (by linarith) (by norm_num)
  unfold Q2
  rw [← hs]
  linarith

lemma Q2_L {P : Params} (h : P.Standing)
    (hb : P.b ≤ (P.a - P.c) * (P.thL + P.thH - 1) / (16 * P.a))
    (hδ : (P.a - P.c) * (1 - (P.thL + P.thH - 1) / 8) ≤ P.delta) :
    Q2 P ≤ -((P.a - P.c) * (P.thL + P.thH - 1) / 4) := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have ha : 0 < P.a := by linarith
  have hA := Ae_hi P hb0 hb1 hc ha.le
  have he := eC_lo P hb0 hb1
  have hf := fC_hi P hb0 hb1
  set σ := P.thL + P.thH - 1 with hσ
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ ≤ 1 := by linarith
  set u := P.a - P.c with hu
  have hu0 : 0 < u := by linarith
  have hδu : P.delta ≤ u := by linarith
  -- b * (2a) ≤ u σ / 8
  have hb2 : P.b * (2 * P.a) ≤ u * σ / 8 := by
    rw [le_div_iff₀ (by positivity)] at hb; linarith
  -- f δ ≤ b u / 3
  have k1 : fC P * P.delta ≤ P.b / 3 * u :=
    mul_le_mul hf hδu hd.le (by positivity)
  -- e δ s ≥ (1/2 - b/6) δ s
  have k2 : (1 / 2 - P.b / 6) * (P.delta * (1 + σ)) ≤ eC P * (P.delta * (1 + σ)) :=
    mul_le_mul_of_nonneg_right he (by positivity)
  -- δ (1 + σ) ≥ u (1 + 3σ/4)
  have k3 : u * (1 + 3 * σ / 4) ≤ P.delta * (1 + σ) := by
    have : u * (1 - σ / 8) * (1 + σ) ≤ P.delta * (1 + σ) :=
      mul_le_mul_of_nonneg_right hδ (by linarith)
    linarith [mul_nonneg hu0.le (mul_nonneg hσ0.le (sub_nonneg.2 hσ1))]
  have k4 : P.b / 6 * (P.delta * (1 + σ)) ≤ P.b / 6 * (u * 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hδu (by linarith) (by linarith) hu0.le) (by positivity)
  have hQ : Q2 P = Ae P + fC P * P.delta - eC P * (P.delta * (1 + σ)) := by
    unfold Q2; rw [hσ]; ring
  rw [hQ]
  have k5 : P.b * (P.a + P.c) / 2 + P.b / 3 * u + P.b / 6 * (u * 2) ≤ P.b * (2 * P.a) := by
    linarith [mul_nonneg hb0 hc, mul_nonneg hb0 ha.le]
  linarith

lemma Aprime_le {P : Params} (h : P.Standing) : Ae P + fC P * P.delta ≤ 4 / 3 * P.a := by
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := h
  have := Ae_le_a P hb0 hb1 hc (by linarith)
  have hf := fC_le P hb1 hb0
  have : fC P * P.delta ≤ 1 / 3 * P.a := mul_le_mul hf (by linarith) hd.le (by norm_num)
  linarith

lemma deltaLow_le (P : Params) (hbase : BaseStanding P.a P.c P.gamma P.thL P.thH P.rho P.lam)
    (hb0 : 0 ≤ P.b) (hb1 : P.b ≤ 1) (hk0 : 0 < P.kappa) :
    deltaLow P ≤ P.gamma ^ 2 * P.a / P.kappa := by
  obtain ⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩ := hbase
  have ha : 0 < P.a := by linarith
  rw [deltaLow_eq P hb1 hb0 hk0 hl0 hl1 hr0 hr1]
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have hf := fC_nonneg P hb1 hb0
  have hf3 := fC_le P hb1 hb0
  have r1 : 0 < 1 - P.rho := by linarith
  have hlam2 : 0 < (1 - P.lam) ^ 2 := by have : 0 < 1 - P.lam := by linarith
                                         positivity
  have hlam3 : 0 < P.lam ^ 2 := by positivity
  have hthH : 0 < P.thH := by linarith
  have hR0 : 0 < R0 P := by unfold R0; positivity
  have hS00 : 0 < S00 P := by unfold S00; positivity
  have hS20 : 0 < S20 P := by unfold S20; positivity
  have hAe : 0 < Ae P := by
    unfold Ae
    apply div_pos _ (by linarith)
    linarith [mul_nonneg hb0 hc]
  have hAa := Ae_le_a P hb0 hb1 hc ha.le
  have s00 : S00 P ≤ R0 P := by
    unfold S00 R0
    linarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (by linarith : 0 ≤ 1 - P.thL),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (by linarith : 0 ≤ 1 - P.thH)]
  have s20 : S20 P ≤ S00 P := by
    unfold S20 S00
    have h1 : P.thL ^ 2 ≤ P.thL := by nlinarith only [hL, hLH, hH1]
    have h2 : P.thH ^ 2 ≤ P.thH := by nlinarith only [hL, hLH, hH1]
    linarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (sub_nonneg.2 h2)]
  have b1 : eC P * S00 P + fC P * S20 P ≤ R0 P := by
    have q1 := mul_le_mul he s00 hS00.le (by norm_num)
    have q2 := mul_le_mul hf3 (s20.trans s00) hS20.le (by norm_num)
    linarith
  have b2 : Ae P * (eC P * S00 P + fC P * S20 P) ≤ P.a * R0 P :=
    mul_le_mul hAa b1 (by positivity) ha.le
  rw [div_le_div_iff₀ (by positivity) hk0]
  have hg2 : 0 < P.gamma ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left b2 hg2.le
  have := mul_le_mul_of_nonneg_right this hk0.le
  linarith

lemma Vc_congr (P P' : Params) (h1 : P.rho = P'.rho) (h2 : P.lam = P'.lam) : Vc P = Vc P' := by
  unfold Vc hH Pcc
  simp only [cell_P, al, signalProb, h1, h2]

end CyberShare.Sharing.P2


open CyberShare.Sharing CyberShare.Sharing.P2

theorem solution (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      (∃ bLow : ℝ, 0 < bLow ∧ bLow ≤ 1 ∧ ∀ b : ℝ, 0 < b → b < bLow →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        (∃ delta1 : ℝ, delta1 < a - c ∧
          ∀ delta : ℝ, delta1 < delta → 0 < delta → delta < a - c →
            IsSharingEq { P0 with delta := delta } .S .S ∧
            ∀ s1 s2 : Dec, IsSharingEq { P0 with delta := delta } s1 s2 →
              s1 = .S ∧ s2 = .S) ∧
        (∃ delta2 : ℝ, deltaLow P0 < delta2 ∧
          ∀ delta : ℝ, deltaLow P0 < delta → delta < delta2 → delta < a - c →
            IsSharingEq { P0 with delta := delta } .N .N ∧
            ∀ s1 s2 : Dec, IsSharingEq { P0 with delta := delta } s1 s2 →
              s1 = .N ∧ s2 = .N)) ∧
      (∃ bHigh : ℝ, 0 ≤ bHigh ∧ bHigh < 1 ∧ ∀ b : ℝ, bHigh < b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          IsSharingEq P .N .N ∧
          ∀ s1 s2 : Dec, IsSharingEq P s1 s2 → s1 = .N ∧ s2 = .N) := by
  have hbase := h
  obtain ⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩ := h
  have hσ0 : 0 < thL + thH - 1 := by linarith
  have hσ1 : thL + thH - 1 ≤ 1 := by linarith
  have hu : 0 < a - c := by linarith
  have ha : 0 < a := by linarith
  set σ := thL + thH - 1 with hσ
  set m0 := (a - c) * σ / 4 with hm0
  have hm0p : 0 < m0 := by positivity
  let Ps : Params := ⟨a, 0, c, (a - c) / 2, gamma, 1, thL, thH, rho, lam⟩
  have hPs : Ps.Standing :=
    ⟨hbase, le_refl _, by norm_num, by show 0 < (a - c) / 2; positivity,
      by show c + (a - c) / 2 < a; linarith, by norm_num⟩
  have hV : 0 < Vc Ps := Vc_pos Ps hPs
  have hD : 0 < (thH - thL) ^ 2 := by have : 0 < thH - thL := by linarith
                                      positivity
  set G := (thH - thL) ^ 2 * Vc Ps * m0 with hG
  have hG0 : 0 < G := by positivity
  have hg2 : 0 < gamma ^ 2 := by positivity
  refine ⟨2 * gamma ^ 2 + 4 * gamma ^ 2 * a / (a - c) + 6 * a * gamma ^ 2 / G, by positivity, ?_⟩
  intro kappa hk
  have t2 : 0 ≤ 4 * gamma ^ 2 * a / (a - c) := by positivity
  have t3 : 0 ≤ 6 * a * gamma ^ 2 / G := by positivity
  have hk1 : 2 * gamma ^ 2 < kappa := by linarith
  have hk2 : 4 * gamma ^ 2 * a / (a - c) < kappa := by linarith
  have hk3 : 6 * a * gamma ^ 2 / G < kappa := by linarith
  have hk0 : 0 < kappa := by linarith
  have hk2' : gamma ^ 2 * a / kappa < (a - c) / 4 := by
    rw [div_lt_iff₀ hu] at hk2
    rw [div_lt_iff₀ hk0]; linarith
  have hkb : gamma ^ 2 * a / (a - c) < kappa := by
    have : gamma ^ 2 * a / (a - c) ≤ 4 * gamma ^ 2 * a / (a - c) := by
      apply div_le_div_of_nonneg_right _ hu.le; nlinarith only [hg2, ha]
    linarith
  -- uniform facts about deltaLow
  have dl : ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      0 < deltaLow ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ ∧
      deltaLow ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ < a - c ∧
      deltaLow ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ < (a - c) / 4 := by
    intro b hb0 hb1
    obtain ⟨d1, d2⟩ := deltaLow_bounds ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ hbase hb0 hb1 hkb
    have d3 := deltaLow_le ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ hbase hb0 hb1 hk0
    exact ⟨d1, d2, lt_of_le_of_lt d3 hk2'⟩
  -- the core
  have gen : ∀ b delta : ℝ, 0 < b → b ≤ 1 →
      deltaLow ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ < delta → delta < a - c →
      (m0 ≤ Q2 ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ →
        IsSharingEq ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ .N .N ∧
        ∀ s1 s2 : Dec, IsSharingEq ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ s1 s2 →
          s1 = .N ∧ s2 = .N) ∧
      (Q2 ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ ≤ -m0 →
        IsSharingEq ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ .S .S ∧
        ∀ s1 s2 : Dec, IsSharingEq ⟨a, b, c, delta, gamma, kappa, thL, thH, rho, lam⟩ s1 s2 →
          s1 = .S ∧ s2 = .S) := by
    intro b δ hb0 hb1 hdl hδ
    set P : Params := ⟨a, b, c, δ, gamma, kappa, thL, thH, rho, lam⟩ with hP
    have hδ0 : 0 < δ := lt_trans (dl b hb0.le hb1).1 hdl
    have hS : P.Standing := ⟨hbase, hb0.le, hb1, hδ0, by show c + δ < a; linarith, hk0⟩
    have hdl' : deltaLow P < P.delta := hdl
    have hHy : Hy P := ⟨hS, hk1, hdl'⟩
    have hb : 0 < P.b := hb0
    have hε : 9 * eps P * (Ae P + fC P * P.delta) < 2 * DD P ^ 2 * m0 * Vc P := by
      have hA := Aprime_le hS
      have hVc : Vc P = Vc Ps := Vc_congr P Ps rfl rfl
      have hDD : DD P = thH - thL := rfl
      have he : eps P = gamma ^ 2 / kappa := rfl
      rw [hVc, hDD, he]
      have hAp : 0 ≤ Ae P + fC P * P.delta := by
        have q1 := Ae_ge P hb1 hb0.le hc (show c + δ < a by linarith) hδ0
        have q2 := mul_pos (eC_pos P hb1 hb0.le) hδ0
        have q3 := mul_nonneg (fC_nonneg P hb1 hb0.le) hδ0.le
        linarith
      have k1 : 9 * (gamma ^ 2 / kappa) * (Ae P + fC P * P.delta) ≤
          9 * (gamma ^ 2 / kappa) * (4 / 3 * P.a) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have k2 : 9 * (gamma ^ 2 / kappa) * (4 / 3 * P.a) < 2 * G := by
        have : P.a = a := rfl
        rw [this]
        rw [div_lt_iff₀ hG0] at hk3
        have e : 9 * (gamma ^ 2 / kappa) * (4 / 3 * a) = 12 * a * gamma ^ 2 / kappa := by
          field_simp; ring
        rw [e, div_lt_iff₀ hk0]; linarith only [hk3]
      have : 2 * G = 2 * (thH - thL) ^ 2 * m0 * Vc Ps := by rw [hG]; ring
      linarith only [k1, k2, this]
    constructor
    · intro hQ
      exact nonshare_unique hHy (fun o K1X K2X K1Y K2Y hX hY =>
        gap_neg hHy hb o m0 hm0p hQ hε K1X K2X K1Y K2Y hX hY)
    · intro hQ
      exact share_unique hHy (fun o K1X K2X K1Y K2Y hX hY =>
        gap_pos hHy hb o m0 hm0p hQ hε K1X K2X K1Y K2Y hX hY)
  have huσ : (a - c) * σ ≤ (a - c) * 1 := mul_le_mul_of_nonneg_left hσ1 hu.le
  have huσ0 : 0 < (a - c) * σ := mul_pos hu hσ0
  have hm0le : m0 ≤ (a - c) / 4 := by
    rw [hm0]; linarith only [huσ]
  refine ⟨⟨(a - c) * σ / (16 * a), by positivity, ?_, ?_⟩, ⟨14 / 15, by norm_num, by norm_num, ?_⟩⟩
  · rw [div_le_one (by positivity)]; linarith only [huσ, hc, ha]
  · intro b hb0 hbL
    have hbL1 : (a - c) * σ / (16 * a) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith only [huσ, hc, ha]
    have hb1 : b ≤ 1 := by linarith
    obtain ⟨d1, d2, d3⟩ := dl b hb0.le hb1
    refine ⟨d1, d2, ⟨(a - c) * (1 - σ / 8), by linarith only [huσ0], ?_⟩, ⟨(a - c) / 4, d3, ?_⟩⟩
    · intro δ hδ1 hδ0 hδ
      have hdl : deltaLow ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩ < δ := by
        have : (a - c) / 4 ≤ (a - c) * (1 - σ / 8) := by linarith only [huσ, hu]
        linarith
      have hS : (⟨a, b, c, δ, gamma, kappa, thL, thH, rho, lam⟩ : Params).Standing :=
        ⟨hbase, hb0.le, hb1, hδ0, by show c + δ < a; linarith, hk0⟩
      have hQ := Q2_L hS (by show b ≤ (a - c) * (thL + thH - 1) / (16 * a); exact hbL.le)
        (by show (a - c) * (1 - (thL + thH - 1) / 8) ≤ δ; exact hδ1.le)
      exact (gen b δ hb0 hb1 hdl hδ).2 hQ
    · intro δ hdl hδ2 hδ
      have hδ0 : 0 < δ := lt_trans d1 hdl
      have hS : (⟨a, b, c, δ, gamma, kappa, thL, thH, rho, lam⟩ : Params).Standing :=
        ⟨hbase, hb0.le, hb1, hδ0, by show c + δ < a; linarith, hk0⟩
      have hQ := Q2_small hS (by show δ ≤ (a - c) / 4; exact hδ2.le)
      exact (gen b δ hb0 hb1 hdl hδ).1 (le_trans hm0le hQ)
  · intro b hbH hb1
    have hb0 : 0 < b := by linarith
    obtain ⟨d1, d2, d3⟩ := dl b hb0.le hb1
    refine ⟨d1, d2, ?_⟩
    intro δ hdl hδ
    have hδ0 : 0 < δ := lt_trans d1 hdl
    have hS : (⟨a, b, c, δ, gamma, kappa, thL, thH, rho, lam⟩ : Params).Standing :=
      ⟨hbase, hb0.le, hb1, hδ0, by show c + δ < a; linarith, hk0⟩
    have hQ := Q2_H hS (by show 14 / 15 ≤ b; linarith)
    have : m0 ≤ a / 3 := by
      have : (a - c) / 4 ≤ a / 3 := by linarith
      linarith
    exact (gen b δ hb0 hb1 hdl hδ).1 (le_trans this hQ)
