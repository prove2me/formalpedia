-- Prove2me | solution 1 for CyberShare.Sharing.lemma_c1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:21:13.130551+00:00
-- url     : https://prove2.me/submissions/fa276ed5-d67b-4fe3-a460-142d5d6ff587

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

open CyberShare.Sharing

noncomputable section
namespace CyberShare.Sharing.C1

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
  have h2 : (4 - b ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 + b) ≠ 0 := by linarith
  have h4 : 4 - b ^ 2 = (2 - b) * (2 + b) := by ring
  rw [h4] at h2 ⊢
  field_simp
  ring

lemma payoff1_eq (P : Params) (hb : P.b ≤ 1) (hb0 : 0 ≤ P.b) (K1 K2 : Sig → Sig → ℝ) (w : Outcome) :
    payoff1 P K1 K2 w =
      (Ae P - eC P * dd P w.attack1 (K1 w.y1 w.y2) + fC P * dd P w.attack2 (K2 w.y2 w.y1)) ^ 2
        - P.kappa * (K1 w.y1 w.y2) ^ 2 := by
  unfold payoff1 profit pStar
  simp only [cost, dd, Ae, eC, fC]
  cases h1 : w.attack1 <;> cases h2 : w.attack2 <;> simp only [if_true, if_false, Bool.false_eq_true]
  all_goals
    have h1 : (2 - P.b) ≠ 0 := by linarith
    have h2 : (4 - P.b ^ 2) ≠ 0 := by nlinarith
    generalize pos (P.delta - P.gamma * K1 w.y1 w.y2) = d1
    generalize pos (P.delta - P.gamma * K2 w.y2 w.y1) = d2
    field_simp
    ring

def Gabs (e g d k S0 S1 Pc U2 x : ℝ) : ℝ :=
  U2 - 2 * e * S1 * max (d - g * x) 0 + e ^ 2 * S0 * (max (d - g * x) 0) ^ 2 - k * Pc * x ^ 2

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
  unfold Gabs
  by_cases hcase : 0 ≤ d - g * x
  · rw [max_eq_left hcase]
    nlinarith [hx]
  · have hcase := not_le.mp hcase
    rw [max_eq_right hcase.le]
    have : 0 ≤ -2 * e * S1 * (d - g * x) + e ^ 2 * S0 * (d - g * x) ^ 2 := by
      have h1 : 0 ≤ e * S1 * (g * x - d) := by
        apply mul_nonneg (mul_nonneg he.le hS1); linarith
      have h2 : 0 ≤ e ^ 2 * S0 * (d - g * x) ^ 2 := by positivity
      nlinarith
    nlinarith [hx]



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
  nlinarith [mul_nonneg hb0 hc]

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
  nlinarith

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
  have h3 : (4 - P.b ^ 2) ≠ 0 := by nlinarith
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
    have h2 : (ind w.attack1) ^ 2 = ind w.attack1 := by nlinarith
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
    exact max_le (by nlinarith [mul_nonneg hg.le hx]) hd.le

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
  · rw [e1, e2]; nlinarith [mul_pos r1 aL, mul_pos hr0 aH, mul_nonneg (mul_pos r1 aL).le (by linarith : 0 ≤ 1 - P.thL),
      mul_nonneg (mul_pos hr0 aH).le (by linarith : 0 ≤ 1 - P.thH)]
  · rw [e2, e3]
    have h1 : P.thL ^ 2 ≤ P.thL := by nlinarith
    have h2 : P.thH ^ 2 ≤ P.thH := by nlinarith
    nlinarith [mul_nonneg (mul_pos r1 aL).le (sub_nonneg.2 h1), mul_nonneg (mul_pos hr0 aH).le (sub_nonneg.2 h2)]
  · rw [e1, e2]
    have := cmp_abs (1 - P.rho) P.rho P.thL P.thH P.lam (al P o y y' .L) (al P o y y' .H) r1.le hr0.le hLH.le rat
    unfold S00 R0
    nlinarith [this]
  · rw [e1, e3]
    have := cmp_abs (1 - P.rho) P.rho (P.thL ^ 2) (P.thH ^ 2) P.lam (al P o y y' .L) (al P o y y' .H) r1.le hr0.le
      (by nlinarith) rat
    unfold S20 R0
    nlinarith [this]

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
  nlinarith [mul_nonneg hf hdd, mul_nonneg hp hi, mul_nonneg (mul_nonneg hp hi) (mul_nonneg hf hdd)]

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
  nlinarith [mul_le_mul_of_nonneg_left h3 h4]

lemma Cq_pos (h : Hy P) (o : Dec) (y y' : Sig) :
    0 < P.kappa * Pcc P o y y' - (eC P) ^ 2 * P.gamma ^ 2 * S0c P o y y' := by
  obtain ⟨hS, hk2, _⟩ := h
  obtain ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ := hS
  obtain ⟨hP, hS0, hle, -⟩ := cell_facts ⟨⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩, hb0, hb1, hd, hcd, hk⟩ o y y'
  have he := eC_le P hb1 hb0
  have he0 := eC_pos P hb1 hb0
  have : (eC P) ^ 2 ≤ 1 / 4 := by nlinarith
  have hg2 : 0 < P.gamma ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hg2.le hS0.le), mul_nonneg hg2.le (sub_nonneg.2 hle),
    mul_pos hP hg2]

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
  have hS1 : 0 ≤ S1c P o y y' B := by nlinarith [mul_pos hA0 hS0]
  have hR0 : 0 < R0 P := by
    unfold R0
    have : 0 < (1 - P.rho) * (1 - P.lam) ^ 2 := by
      apply mul_pos (by linarith); apply pow_pos; linarith
    have : 0 < P.rho * P.lam ^ 2 := by positivity
    linarith
  refine ⟨hS1, ?_, ?_⟩
  · unfold br
    apply div_pos _ hC
    have : 0 < Ae P - eC P * P.delta := by linarith
    have : 0 < eC P * P.gamma := by positivity
    apply mul_pos this
    nlinarith [mul_pos this hS0]
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
      nlinarith [mul_le_mul_of_nonneg_left c0 (hA0.le),
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
      nlinarith [mul_pos hC hcon]
    have : A y y' - br P o y y' B = 0 := by nlinarith [sq_nonneg (A y y' - br P o y y' B)]
    linarith
  · intro hbr y y' x hx
    obtain ⟨hS1, hpos, hlt⟩ := br_bounds h o y y' B hB
    have hC := Cq_pos h o y y'
    have hS0 := (cell_facts h.1 o y y').2.1
    have m := maxQ (eC P) P.gamma P.delta P.kappa (S0c P o y y') (S1c P o y y' B) (Pcc P o y y')
      (U2c P o y y' B) he0 hg hS1 hS0.le hC hlt x
    rw [obj_eq P hb1 hb0, cur_eq hb1 hb0 o A B hA, hbr y y']
    unfold br at m ⊢
    nlinarith [mul_nonneg hC.le (sq_nonneg (x - eC P * P.gamma * (S1c P o y y' B - eC P * P.delta * S0c P o y y') /
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
  nlinarith [mul_pos h1 hS0]

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
  have hee : eC P ^ 2 ≤ 1 / 4 := by nlinarith
  have hef : eC P * fC P ≤ 1 / 6 := by nlinarith
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
    nlinarith [mul_nonneg hb0 hc]
  have hAa : Ae P ≤ P.a := by
    unfold Ae
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hb0 hc, mul_nonneg hb0 (by linarith : 0 ≤ P.a), mul_nonneg hb0 hb0]
  have s00 : S00 P ≤ R0 P := by
    unfold S00 R0
    nlinarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (by linarith : 0 ≤ 1 - P.thL),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (by linarith : 0 ≤ 1 - P.thH)]
  have s20 : S20 P ≤ S00 P := by
    unfold S20 S00
    have h1 : P.thL ^ 2 ≤ P.thL := by nlinarith
    have h2 : P.thH ^ 2 ≤ P.thH := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg r1.le hlam2.le) (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg hr0.le hlam3.le) (sub_nonneg.2 h2)]
  constructor
  · apply div_pos _ (by positivity)
    positivity
  · rw [div_lt_iff₀ (by positivity)]
    have hk' : P.gamma ^ 2 * P.a < P.kappa * (P.a - P.c) := by
      rwa [div_lt_iff₀ hac] at hk
    have b1 : eC P * S00 P + fC P * S20 P ≤ R0 P := by nlinarith
    have b2 : Ae P * (eC P * S00 P + fC P * S20 P) ≤ P.a * R0 P := by
      apply mul_le_mul hAa b1 (by positivity) (by linarith)
    have hg2 : 0 < P.gamma ^ 2 := by positivity
    have b3 := mul_le_mul_of_nonneg_left b2 hg2.le
    have b4 : P.gamma ^ 2 * P.a * R0 P < P.kappa * (P.a - P.c) * R0 P := mul_lt_mul_of_pos_right hk' hR0
    nlinarith

theorem lemma_c1_main (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          ∀ s1 s2 : Dec,
            ∃ pair : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
              IsInvEq P s1 s2 pair.1 pair.2 ∧
              (∀ y y' : Sig, 0 < pair.1 y y' ∧ pair.1 y y' < delta / gamma ∧
                0 < pair.2 y y' ∧ pair.2 y y' < delta / gamma) ∧
              ∀ pair' : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
                IsInvEq P s1 s2 pair'.1 pair'.2 → pair' = pair := by
  have h' := h
  obtain ⟨hc, hg, hL, hLH, hH1, h1H, hr0, hr1, hl0, hl1, hca⟩ := h'
  have hac : 0 < a - c := by linarith
  refine ⟨2 * gamma ^ 2 + gamma ^ 2 * a / (a - c), ?_, ?_⟩
  · have : 0 < a := by linarith
    have : 0 < gamma ^ 2 * a / (a - c) := div_pos (by positivity) hac
    have : 0 < gamma ^ 2 := by positivity
    linarith
  intro kappa hkappa b hb0 hb1
  have hk1 : gamma ^ 2 * a / (a - c) < kappa := by
    have : 0 < gamma ^ 2 := by positivity
    linarith
  have hk2 : 2 * gamma ^ 2 < kappa := by
    have : 0 ≤ gamma ^ 2 * a / (a - c) := by
      have : 0 < a := by linarith
      exact div_nonneg (by positivity) hac.le
    linarith
  have hk0 : 0 < kappa := by
    have : 0 < gamma ^ 2 := by positivity
    linarith
  intro P0
  have hdl := deltaLow_bounds P0 h hb0 hb1 hk1
  refine ⟨hdl.1, hdl.2, ?_⟩
  intro delta hd1 hd2 P s1 s2
  have hdpos : 0 < delta := lt_trans hdl.1 hd1
  have hHy : Hy P := by
    refine ⟨⟨h, hb0, hb1, hdpos, by show c + delta < a; linarith, hk0⟩, hk2, ?_⟩
    exact hd1
  exact exists_unique_inv hHy s1 s2

end CyberShare.Sharing.C1

open CyberShare.Sharing.C1 in
theorem solution (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          ∀ s1 s2 : Dec,
            ∃ pair : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
              IsInvEq P s1 s2 pair.1 pair.2 ∧
              (∀ y y' : Sig, 0 < pair.1 y y' ∧ pair.1 y y' < delta / gamma ∧
                0 < pair.2 y y' ∧ pair.2 y y' < delta / gamma) ∧
              ∀ pair' : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
                IsInvEq P s1 s2 pair'.1 pair'.2 → pair' = pair :=
  lemma_c1_main a c gamma thL thH rho lam h
