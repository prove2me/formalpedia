-- Prove2me | solution 1 for BidPriceControl.NonOptimal.bid_price_controls_not_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:00:12.288592+00:00
-- url     : https://prove2.me/submissions/d2d229c8-2a2b-4a53-8c7a-db1f02bda918

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model
import Definitions.Def_BidPriceControl_NonOptimal_CounterExample

open MeasureTheory

namespace Aux_BidPriceControl_notOptimal
open BidPriceControl.NonOptimal

theorem int2 (f : (Fin 3 → ℝ) → ℝ) (c1 c2 : ENNReal) (h1 : c1 ≠ ⊤) (h2 : c2 ≠ ⊤)
    (x1 x2 : Fin 3 → ℝ) :
    ∫ r, f r ∂(c1 • Measure.dirac x1 + c2 • Measure.dirac x2) =
      c1.toReal * f x1 + c2.toReal * f x2 := by
  have i1 : Integrable f (c1 • Measure.dirac x1) :=
    (integrable_dirac (by simp)).smul_measure h1
  have i2 : Integrable f (c2 • Measure.dirac x2) :=
    (integrable_dirac (by simp)).smul_measure h2
  rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp [smul_eq_mul]

theorem int3 (f : (Fin 3 → ℝ) → ℝ) (c1 c2 c3 : ENNReal) (h1 : c1 ≠ ⊤) (h2 : c2 ≠ ⊤)
    (h3 : c3 ≠ ⊤) (x1 x2 x3 : Fin 3 → ℝ) :
    ∫ r, f r ∂(c1 • Measure.dirac x1 + c2 • Measure.dirac x2 + c3 • Measure.dirac x3) =
      c1.toReal * f x1 + c2.toReal * f x2 + c3.toReal * f x3 := by
  have i1 : Integrable f (c1 • Measure.dirac x1) :=
    (integrable_dirac (by simp)).smul_measure h1
  have i2 : Integrable f (c2 • Measure.dirac x2) :=
    (integrable_dirac (by simp)).smul_measure h2
  have i3 : Integrable f (c3 • Measure.dirac x3) :=
    (integrable_dirac (by simp)).smul_measure h3
  rw [integral_add_measure (i1.add_measure i2) i3, integral_add_measure i1 i2,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac]
  simp [smul_eq_mul]

/-- One-step value of a decision: `none` keeps capacity, `some j` sells `j`. -/
noncomputable def step (W : (Fin 2 → ℕ) → ℝ) (y : Fin 2 → ℕ) (r : Fin 3 → ℝ) :
    Option (Fin 3) → ℝ
  | none => W y
  | some j => r j + W (y - column ceA j)

theorem cv1 (u : Control 2 3) (y : Fin 2 → ℕ) :
    controlValue ceA ceLaw u 1 y =
      4 / 5 * step (fun _ => 0) y ![500, 0, 0] (u 1 y ![500, 0, 0]) +
      1 / 5 * step (fun _ => 0) y ![0, 0, 0] (u 1 y ![0, 0, 0]) := by
  have ne1 : (4 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have ne2 : (1 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have t1 : (4 / 5 : ENNReal).toReal = 4 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have t2 : (1 / 5 : ENNReal).toReal = 1 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have h := int2 (fun r => step (fun _ => 0) y r (u 1 y r)) _ _ ne1 ne2
    ![500, 0, 0] ![0, 0, 0]
  rw [t1, t2] at h
  rw [← h]
  rw [controlValue]
  congr 1
  funext r
  cases u 1 y r <;> rfl

theorem cv2 (u : Control 2 3) :
    controlValue ceA ceLaw u 2 ceX =
      2 / 5 * step (controlValue ceA ceLaw u 1) ceX ![500, 0, 0] (u 2 ceX ![500, 0, 0]) +
      3 / 10 * step (controlValue ceA ceLaw u 1) ceX ![0, 250, 0] (u 2 ceX ![0, 250, 0]) +
      3 / 10 * step (controlValue ceA ceLaw u 1) ceX ![0, 0, 250] (u 2 ceX ![0, 0, 250]) := by
  have n1 : (2 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have n2 : (3 / 10 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have u1 : (2 / 5 : ENNReal).toReal = 2 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have u2 : (3 / 10 : ENNReal).toReal = 3 / 10 := by rw [ENNReal.toReal_div]; norm_num
  have h := int3 (fun r => step (controlValue ceA ceLaw u 1) ceX r (u 2 ceX r)) _ _ _ n1 n2 n2
    ![500, 0, 0] ![0, 250, 0] ![0, 0, 250]
  rw [u1, u2] at h
  rw [← h]
  rw [controlValue]
  congr 1
  funext r
  cases u 2 ceX r <;> rfl

/-- Period-1 bounds for any control whose decisions fit. -/
theorem v1_bound (u : Control 2 3) (hfit : ∀ t y r j, u t y r = some j → Fits ceA y j)
    (y : Fin 2 → ℕ) :
    controlValue ceA ceLaw u 1 y ≤ 400 ∧
      (¬ Fits ceA y 0 → controlValue ceA ceLaw u 1 y ≤ 0) := by
  rw [cv1]
  have hb : ∀ o, u 1 y ![500, 0, 0] = o →
      step (fun _ => 0) y ![500, 0, 0] o ≤ 500 ∧
        (¬ Fits ceA y 0 → step (fun _ => 0) y ![500, 0, 0] o ≤ 0) := by
    intro o ho
    cases o with
    | none => simp [step]
    | some j =>
      have hf := hfit _ _ _ _ ho
      fin_cases j
      · simp [step]
        intro h; exact absurd hf h
      · simp [step]
      · simp [step]
  have hc : ∀ o, step (fun _ => 0) y ![0, 0, 0] o ≤ 0 := by
    intro o
    cases o with
    | none => simp [step]
    | some j => fin_cases j <;> simp [step]
  obtain ⟨h1, h2⟩ := hb _ rfl
  have h3 := hc (u 1 y ![0, 0, 0])
  refine ⟨by linarith, fun hn => ?_⟩
  have := h2 hn
  linarith

theorem notfit00 : ¬ Fits ceA (ceX - column ceA 0) 0 := by decide
theorem notfit01 : ¬ Fits ceA (ceX - column ceA 1) 0 := by decide
theorem notfit02 : ¬ Fits ceA (ceX - column ceA 2) 0 := by decide

/-- Period-2 bounds on each outcome, for any control whose decisions fit. -/
theorem step_a (u : Control 2 3) (hfit : ∀ t y r j, u t y r = some j → Fits ceA y j)
    (o : Option (Fin 3)) :
    step (controlValue ceA ceLaw u 1) ceX ![500, 0, 0] o ≤ 500 := by
  cases o with
  | none => have := (v1_bound u hfit ceX).1; simp only [step]; linarith
  | some j =>
    fin_cases j
    · have := (v1_bound u hfit _).2 notfit00; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit01; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit02; simp [step]; linarith

theorem step_b (u : Control 2 3) (hfit : ∀ t y r j, u t y r = some j → Fits ceA y j)
    (o : Option (Fin 3)) :
    step (controlValue ceA ceLaw u 1) ceX ![0, 250, 0] o ≤ 400 := by
  cases o with
  | none => have := (v1_bound u hfit ceX).1; simp only [step]; linarith
  | some j =>
    fin_cases j
    · have := (v1_bound u hfit _).2 notfit00; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit01; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit02; simp [step]; linarith

theorem step_c (u : Control 2 3) (hfit : ∀ t y r j, u t y r = some j → Fits ceA y j)
    (o : Option (Fin 3)) :
    step (controlValue ceA ceLaw u 1) ceX ![0, 0, 250] o ≤ 400 := by
  cases o with
  | none => have := (v1_bound u hfit ceX).1; simp only [step]; linarith
  | some j =>
    fin_cases j
    · have := (v1_bound u hfit _).2 notfit00; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit01; simp [step]; linarith
    · have := (v1_bound u hfit _).2 notfit02; simp [step]; linarith

theorem upper440 (u : Control 2 3) (hfit : ∀ t y r j, u t y r = some j → Fits ceA y j) :
    controlValue ceA ceLaw u 2 ceX ≤ 440 := by
  rw [cv2]
  have := step_a u hfit (u 2 ceX ![500, 0, 0])
  have := step_b u hfit (u 2 ceX ![0, 250, 0])
  have := step_c u hfit (u 2 ceX ![0, 0, 250])
  linarith

/-- Accept the through request whenever it fits. -/
noncomputable def uThrough : Control 2 3 := fun _ y r =>
  if Fits ceA y 0 then (if 0 < r 0 then some 0 else none) else none

theorem uThrough_adm : IsAdmissible ceA uThrough := by
  constructor
  · intro t y r j h
    unfold uThrough at h
    split_ifs at h with h1 h2
    · cases h; exact h1
  · intro t y j
    by_cases h1 : Fits ceA y 0
    · by_cases hj : j = 0
      · subst hj
        have : {r : Fin 3 → ℝ | uThrough t y r = some 0} = {r | 0 < r 0} := by
          ext r; simp [uThrough, h1]
        rw [this]
        exact measurableSet_lt measurable_const (measurable_pi_apply 0)
      · have : {r : Fin 3 → ℝ | uThrough t y r = some j} = ∅ := by
          ext r
          simp only [uThrough, h1, if_true, Set.mem_empty_iff_false, iff_false]
          show ¬ ((if 0 < r 0 then some 0 else none) = some j)
          split_ifs
          · intro h; cases h; exact hj rfl
          · simp
        rw [this]; exact MeasurableSet.empty
    · have : {r : Fin 3 → ℝ | uThrough t y r = some j} = ∅ := by
        ext r; simp [uThrough, h1]
      rw [this]; exact MeasurableSet.empty

theorem uThrough_val : controlValue ceA ceLaw uThrough 2 ceX = 440 := by
  have hX : Fits ceA ceX 0 := by decide
  have h1X : controlValue ceA ceLaw uThrough 1 ceX = 400 := by
    rw [cv1]; simp [uThrough, hX, step]; norm_num
  have h100 : controlValue ceA ceLaw uThrough 1 (ceX - column ceA 0) = 0 := by
    rw [cv1]; simp [uThrough, notfit00, step]
  rw [cv2]
  simp only [uThrough, hX, if_true]
  simp [step, h1X, h100]
  norm_num

/-! Bid-price controls. -/

theorem bp_some {A : Fin 2 → Fin 3 → ℕ} {μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ} {t : ℕ}
    {y : Fin 2 → ℕ} {r : Fin 3 → ℝ} {j : Fin 3} (h : bidPriceControl A μ t y r = some j) :
    0 < r j ∧ Fits A y j ∧ bidPriceSum A μ t y j ≤ r j := by
  unfold bidPriceControl at h
  simp only at h
  split_ifs at h with hS
  cases h
  have := Finset.min'_mem _ hS
  simpa using this

theorem bp_none {A : Fin 2 → Fin 3 → ℕ} {μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ} {t : ℕ}
    {y : Fin 2 → ℕ} {r : Fin 3 → ℝ} (h : bidPriceControl A μ t y r = none) (j : Fin 3) :
    ¬ (0 < r j ∧ Fits A y j ∧ bidPriceSum A μ t y j ≤ r j) := by
  unfold bidPriceControl at h
  simp only at h
  split_ifs at h with hS
  intro hj
  exact hS ⟨j, by simpa using hj⟩

theorem bp_eq_none {A : Fin 2 → Fin 3 → ℕ} {μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ} {t : ℕ}
    {y : Fin 2 → ℕ} {r : Fin 3 → ℝ}
    (h : ∀ j, ¬ (0 < r j ∧ Fits A y j ∧ bidPriceSum A μ t y j ≤ r j)) :
    bidPriceControl A μ t y r = none := by
  cases hc : bidPriceControl A μ t y r with
  | none => rfl
  | some j => exact absurd (bp_some hc) (h j)

theorem bp_eq_some {A : Fin 2 → Fin 3 → ℕ} {μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ} {t : ℕ}
    {y : Fin 2 → ℕ} {r : Fin 3 → ℝ} {j : Fin 3}
    (hj : 0 < r j ∧ Fits A y j ∧ bidPriceSum A μ t y j ≤ r j)
    (huniq : ∀ j', 0 < r j' → j' = j) :
    bidPriceControl A μ t y r = some j := by
  cases hc : bidPriceControl A μ t y r with
  | none => exact absurd hj (bp_none hc j)
  | some j' => rw [huniq j' (bp_some hc).1]

theorem bp_fit (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) :
    ∀ t y r j, bidPriceControl ceA μ t y r = some j → Fits ceA y j :=
  fun _ _ _ _ h => (bp_some h).2.1

theorem bps0 (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) (t : ℕ) (y : Fin 2 → ℕ) :
    bidPriceSum ceA μ t y 0 = μ t y 0 + μ t y 1 := by
  simp [bidPriceSum, Fin.sum_univ_two, ceA]

theorem bps1 (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) (t : ℕ) (y : Fin 2 → ℕ) :
    bidPriceSum ceA μ t y 1 = μ t y 0 := by
  simp [bidPriceSum, Fin.sum_univ_two, ceA]

theorem bps2 (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) (t : ℕ) (y : Fin 2 → ℕ) :
    bidPriceSum ceA μ t y 2 = μ t y 1 := by
  simp [bidPriceSum, Fin.sum_univ_two, ceA]

theorem bp_upper (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) :
    controlValue ceA ceLaw (bidPriceControl ceA μ) 2 ceX ≤ 400 := by
  set u := bidPriceControl ceA μ with hu
  have hfit := bp_fit μ
  have hW := (v1_bound u hfit ceX).1
  have hX : Fits ceA ceX 0 ∧ Fits ceA ceX 1 ∧ Fits ceA ceX 2 := by decide
  rw [cv2]
  have ha := step_a u hfit (u 2 ceX ![500, 0, 0])
  have hb := step_b u hfit (u 2 ceX ![0, 250, 0])
  have hc := step_c u hfit (u 2 ceX ![0, 0, 250])
  -- outcome b: accepted gives ≤ 250, rejected forces μ₁ > 250
  have hb' : step (controlValue ceA ceLaw u 1) ceX ![0, 250, 0] (u 2 ceX ![0, 250, 0]) ≤ 250 ∨
      (250 < μ 2 ceX 0 ∧
        step (controlValue ceA ceLaw u 1) ceX ![0, 250, 0] (u 2 ceX ![0, 250, 0]) ≤ 400) := by
    cases h : u 2 ceX ![0, 250, 0] with
    | none =>
      right
      refine ⟨?_, by simp only [step]; exact hW⟩
      have := bp_none h 1
      rw [bps1] at this
      by_contra hc'
      exact this ⟨by simp, hX.2.1, by simpa using (not_lt.mp hc')⟩
    | some j =>
      left
      have hs := bp_some h
      have hj : j = 1 := by
        fin_cases j <;> simp at hs ⊢
      subst hj
      have := (v1_bound u hfit _).2 notfit01
      simp [step]; linarith
  have hc' : step (controlValue ceA ceLaw u 1) ceX ![0, 0, 250] (u 2 ceX ![0, 0, 250]) ≤ 250 ∨
      (250 < μ 2 ceX 1 ∧
        step (controlValue ceA ceLaw u 1) ceX ![0, 0, 250] (u 2 ceX ![0, 0, 250]) ≤ 400) := by
    cases h : u 2 ceX ![0, 0, 250] with
    | none =>
      right
      refine ⟨?_, by simp only [step]; exact hW⟩
      have := bp_none h 2
      rw [bps2] at this
      by_contra hc'
      exact this ⟨by simp, hX.2.2, by simpa using (not_lt.mp hc')⟩
    | some j =>
      left
      have hs := bp_some h
      have hj : j = 2 := by
        fin_cases j <;> simp at hs ⊢
      subst hj
      have := (v1_bound u hfit _).2 notfit02
      simp [step]; linarith
  -- outcome a: accepted requires μ₀ + μ₁ ≤ 500, rejected gives the period-1 value
  have ha' : (μ 2 ceX 0 + μ 2 ceX 1 ≤ 500) ∨
      step (controlValue ceA ceLaw u 1) ceX ![500, 0, 0] (u 2 ceX ![500, 0, 0]) ≤ 400 := by
    cases h : u 2 ceX ![500, 0, 0] with
    | none => right; simp only [step]; exact hW
    | some j =>
      left
      have hs := bp_some h
      have hj : j = 0 := by
        fin_cases j <;> simp at hs ⊢
      subst hj
      have := hs.2.2
      rw [bps0] at this
      simpa using this
  rcases hb' with hb' | ⟨hb1, hb2⟩ <;> rcases hc' with hc' | ⟨hc1, hc2⟩ <;>
    rcases ha' with ha' | ha' <;> linarith

/-- Reject everything with two periods to go, accept everything with one period to go. -/
noncomputable def μStar : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ := fun t _ _ => if t = 2 then 1000 else 0

theorem bp_star_val : controlValue ceA ceLaw (bidPriceControl ceA μStar) 2 ceX = 400 := by
  have hX : Fits ceA ceX 0 := by decide
  have n2 : ∀ r : Fin 3 → ℝ, (∀ j, r j ≤ 500) →
      bidPriceControl ceA μStar 2 ceX r = none := by
    intro r hr
    apply bp_eq_none
    intro j hj
    have h := hj.2.2
    fin_cases j
    · change bidPriceSum ceA μStar 2 ceX 0 ≤ r 0 at h
      rw [bps0] at h; simp [μStar] at h; linarith [hr 0]
    · change bidPriceSum ceA μStar 2 ceX 1 ≤ r 1 at h
      rw [bps1] at h; simp [μStar] at h; linarith [hr 1]
    · change bidPriceSum ceA μStar 2 ceX 2 ≤ r 2 at h
      rw [bps2] at h; simp [μStar] at h; linarith [hr 2]
  have hn1 := n2 ![500, 0, 0] (by intro j; fin_cases j <;> norm_num)
  have hn2 := n2 ![0, 250, 0] (by intro j; fin_cases j <;> norm_num)
  have hn3 := n2 ![0, 0, 250] (by intro j; fin_cases j <;> norm_num)
  have hs1 : bidPriceControl ceA μStar 1 ceX ![500, 0, 0] = some 0 := by
    apply bp_eq_some
    · refine ⟨by simp, hX, ?_⟩
      rw [bps0]; simp [μStar]
    · intro j' hj'; fin_cases j' <;> simp at hj' ⊢
  have hs2 : bidPriceControl ceA μStar 1 ceX ![0, 0, 0] = none := by
    apply bp_eq_none
    intro j hj; have := hj.1; fin_cases j <;> simp at this
  have h1X : controlValue ceA ceLaw (bidPriceControl ceA μStar) 1 ceX = 400 := by
    rw [cv1, hs1, hs2]; simp [step]; norm_num
  rw [cv2, hn1, hn2, hn3]
  simp only [step, h1X]
  norm_num

end Aux_BidPriceControl_notOptimal

open BidPriceControl.NonOptimal Aux_BidPriceControl_notOptimal in
theorem solution :
    (∃ u : Control 2 3, IsAdmissible ceA u ∧ controlValue ceA ceLaw u 2 ceX = 440) ∧
    (∀ u : Control 2 3, IsAdmissible ceA u → controlValue ceA ceLaw u 2 ceX ≤ 440) ∧
    IsGreatest {v : ℝ | ∃ μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ,
      v = controlValue ceA ceLaw (bidPriceControl ceA μ) 2 ceX} 400 := by
  refine ⟨⟨uThrough, uThrough_adm, uThrough_val⟩, fun u hu => upper440 u hu.fits, ?_, ?_⟩
  · exact ⟨μStar, bp_star_val.symm⟩
  · rintro v ⟨μ, rfl⟩
    exact bp_upper μ
