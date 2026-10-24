-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T18:32:39.083657+00:00
-- url     : https://prove2.me/submissions/2b5e41e0-cd5d-4f8e-bbb0-9f1028f186a7

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model

set_option autoImplicit false

noncomputable section

namespace GDPRB2

open MeasureTheory Set GDPRDataMarkets.Benchmark

variable (P : Params)

def k1 : ℝ := 1 + P.mu - P.sigma
def al : ℝ := 1 + P.d * P.sigma - P.d / 2
def bt : ℝ := 1 + P.d * P.sigma
def ps : ℝ := P.d * P.c * (P.sigma - 1)
def wA (p1 : ℝ) : ℝ := (p1 + P.c * (1 + P.d / 2)) / al P
def wB (p1 : ℝ) : ℝ := (p1 + P.c * (1 + P.d)) / bt P
def W (p1 : ℝ) : ℝ := if p1 < ps P ∨ 1 ≤ P.c then wB P p1 else wA P p1
def Q (p1 : ℝ) : ℝ := if p1 < ps P ∨ 1 ≤ P.c then 1 else (min (wA P p1) 1 - P.c) / 2
def E : ℝ := 4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma
def vb : ℝ := 2 * (al P + P.c) / E P
def X : ℝ := (1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma)

def prof (p : ℝ) : Profile where
  p1 := p
  p2 := Q P
  r := fun v => (1 + P.mu - P.sigma) * v
  buy := fun p1 v => decide (W P p1 ≤ v)

def PiB (m : ℝ) : ℝ := (1 - m) * (bt P * m - P.c * (1 + P.d)) + P.d * (k1 P * ((1 - m ^ 2) / 2))
def PiA (m : ℝ) : ℝ := (1 - m) * (al P * m - P.c * (1 + P.d / 2)) +
  P.d * (k1 P * ((1 - m ^ 2) / 2) + (m - P.c) / 2 * ((m - P.c) / 2))

lemma basics (hS : P.Standing) (hA : P.Assumption1) :
    0 < P.d ∧ P.d ≤ 1 ∧ 0 ≤ P.c ∧ 0 < P.sigma ∧ P.kL = P.mu - P.sigma ∧
    P.kH = P.mu + P.sigma ∧ (3 + P.d) * P.sigma ≤ P.mu ∧ 1 / 2 + (2 + P.d) * P.sigma ≤ P.mu := by
  obtain ⟨_, h2, h3, h4, h5⟩ := hS
  have hA' := hA
  unfold Params.Assumption1 at hA'
  rw [max_le_iff] at hA'
  refine ⟨h3, h4, h5, ?_, ?_, ?_, hA'.1, hA'.2⟩
  · unfold Params.sigma; linarith
  · unfold Params.mu Params.sigma; ring
  · unfold Params.mu Params.sigma; ring

lemma pos (hS : P.Standing) (hA : P.Assumption1) :
    0 < al P ∧ 0 < bt P ∧ 0 < E P ∧ 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma ∧
    0 < 2 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma ∧ 0 ≤ 1 + P.d * P.sigma - P.d ∧
    0 < P.mu ∧ 0 < P.d * P.sigma ∧ 0 < P.d * P.mu := by
  obtain ⟨hd, hd1, hc, hs, _, _, hA1, hA2⟩ := basics P hS hA
  have hds := mul_pos hd hs
  have hmu : 0 < P.mu := by nlinarith
  have hdm := mul_pos hd hmu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hmu, hds, hdm⟩
  · unfold al; linarith
  · unfold bt; linarith
  · unfold E; linarith
  · linarith
  · linarith
  · linarith

lemma RB_r (hS : P.Standing) (hA : P.Assumption1) {v : ℝ} (hv : 0 ≤ v) :
    RB P v ((1 + P.mu - P.sigma) * v) = (1 + P.mu - P.sigma) * v := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  unfold RB revB
  rw [if_pos (le_of_eq (by rw [hkL]; ring)), if_pos (by rw [hkH]; nlinarith)]
  ring

lemma RB_opt (hS : P.Standing) (hA : P.Assumption1) {v : ℝ} (hv : 0 ≤ v) (ρ : ℝ) :
    RB P v ρ ≤ RB P v ((1 + P.mu - P.sigma) * v) := by
  rw [RB_r P hS hA hv]
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  have h3 : 0 ≤ 1 + P.mu - 3 * P.sigma := by nlinarith [mul_pos hd hs]
  have h1 : 0 ≤ 1 + P.mu - P.sigma := by linarith
  unfold RB revB
  rw [hkL, hkH]
  split_ifs with g1 g2 g2 <;> nlinarith [mul_nonneg h3 hv, mul_nonneg h1 hv]

lemma r_bounds (hS : P.Standing) (hA : P.Assumption1) {v : ℝ} (hv : 0 ≤ v) :
    (1 + P.mu - P.sigma) * v ≤ (1 + P.kL) * v ∧ (1 + P.mu - P.sigma) * v ≤ (1 + P.kH) * v := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  rw [hkL, hkH]
  constructor
  · linarith
  · nlinarith [mul_nonneg hs.le hv]

lemma U1buy_eq (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    U1buy P (prof P p) p1 v = bt P * v - p1 - P.c * (1 + P.d) := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  have e1 : (1 + P.kL) * v - (1 + P.mu - P.sigma) * v - P.c = -P.c := by rw [hkL]; ring
  have e2 : (1 + P.kH) * v - (1 + P.mu - P.sigma) * v - P.c = 2 * P.sigma * v - P.c := by
    rw [hkH]; ring
  have hsv : 0 ≤ 2 * P.sigma * v := by nlinarith
  show v - p1 - P.c + P.d * ((max ((1 + P.kL) * v - (1 + P.mu - P.sigma) * v - P.c) (-P.c) +
    max ((1 + P.kH) * v - (1 + P.mu - P.sigma) * v - P.c) (-P.c)) / 2) = _
  rw [e1, e2, max_self, max_eq_left (by linarith)]
  unfold bt; ring

lemma wA_ge_c (hS : P.Standing) (hA : P.Assumption1) {p1 : ℝ} (h : ps P ≤ p1) : P.c ≤ wA P p1 := by
  obtain ⟨hal, -⟩ := pos P hS hA
  unfold wA; rw [le_div_iff₀ hal]; unfold al; unfold ps at h; nlinarith

lemma cons (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) : ∀ v ∈ Icc (0 : ℝ) 1,
    ((prof P p).buy p1 v = true → U1wait P (prof P p) p1 v ≤ U1buy P (prof P p) p1 v) ∧
    ((prof P p).buy p1 v = false → U1buy P (prof P p) p1 v ≤ U1wait P (prof P p) p1 v) := by
  intro v hv
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, -, -, -, hcoef, -⟩ := pos P hS hA
  rw [U1buy_eq P hS hA p p1 hv.1]
  have hbuy : (prof P p).buy p1 v = decide (W P p1 ≤ v) := rfl
  have hwait : U1wait P (prof P p) p1 v = P.d * max (v - Q P p1 - P.c) 0 := rfl
  rw [hbuy, hwait]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le]
  by_cases hB : p1 < ps P ∨ 1 ≤ P.c
  · have hW : W P p1 = wB P p1 := if_pos hB
    have hQ : Q P p1 = 1 := if_pos hB
    rw [hW, hQ, max_eq_right (by linarith [hv.2] : v - 1 - P.c ≤ 0), mul_zero]
    have key : wB P p1 * bt P = p1 + P.c * (1 + P.d) := by
      unfold wB; exact div_mul_cancel₀ _ hbt.ne'
    constructor
    · intro h; nlinarith [mul_le_mul_of_nonneg_right h hbt.le]
    · intro h; nlinarith [mul_lt_mul_of_pos_right h hbt]
  · have hW : W P p1 = wA P p1 := if_neg hB
    have hQ : Q P p1 = (min (wA P p1) 1 - P.c) / 2 := if_neg hB
    have hps : ps P ≤ p1 := not_lt.1 (not_or.1 hB).1
    have hwc := wA_ge_c P hS hA hps
    rw [hW, hQ]
    have key : wA P p1 * al P = p1 + P.c * (1 + P.d / 2) := by
      unfold wA; exact div_mul_cancel₀ _ hal.ne'
    unfold al at key
    unfold bt
    constructor
    · intro h
      have hm : min (wA P p1) 1 = wA P p1 := min_eq_left (h.trans hv.2)
      rw [hm]
      rcases le_total (v - (wA P p1 - P.c) / 2 - P.c) 0 with h' | h'
      · rw [max_eq_right h', mul_zero]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + P.d * P.sigma) (sub_nonneg.2 h),
          mul_nonneg hd.le (sub_nonneg.2 hwc)]
      · rw [max_eq_left h']
        nlinarith [mul_nonneg hcoef (sub_nonneg.2 h)]
    · intro h
      have hmw : min (wA P p1) 1 ≤ wA P p1 := min_le_left _ _
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hd.le)
      nlinarith [mul_nonneg hcoef (sub_nonneg.2 h.le), mul_nonneg hd.le (sub_nonneg.2 hmw)]

lemma vol_sandwich {s : Set ℝ} {a b : ℝ} (h1 : Ioo a b ⊆ s) (h2 : s ⊆ Icc a b) :
    (volume s).toReal = max (b - a) 0 := by
  have : volume s = ENNReal.ofReal (b - a) :=
    le_antisymm (by rw [← Real.volume_Icc]; exact measure_mono h2)
      (by rw [← Real.volume_Ioo]; exact measure_mono h1)
  rw [this, ENNReal.toReal_ofReal']

lemma buyer_set (p p1 : ℝ) : buyerSet (prof P p) p1 = Icc (max 0 (W P p1)) 1 := by
  ext v
  simp only [buyerSet, prof, mem_setOf_eq, mem_Icc, max_le_iff, decide_eq_true_eq]
  tauto

lemma int_part (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) :
    ∫ v in buyerSet (prof P p) p1, RB P v ((prof P p).r v) =
      k1 P * ((1 - (min (max 0 (W P p1)) 1) ^ 2) / 2) := by
  rw [buyer_set]
  have hc : ∫ v in Icc (max 0 (W P p1)) 1, RB P v ((prof P p).r v) =
      ∫ v in Icc (max 0 (W P p1)) 1, k1 P * v :=
    setIntegral_congr_fun measurableSet_Icc (fun v hv => by
      show RB P v ((1 + P.mu - P.sigma) * v) = _
      rw [RB_r P hS hA ((le_max_left _ _).trans hv.1)]; rfl)
  rw [hc]
  by_cases h : max 0 (W P p1) ≤ 1
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_const_mul, integral_id, min_eq_left h]
    ring
  · rw [Icc_eq_empty h, setIntegral_empty, min_eq_right (le_of_lt (not_le.1 h))]
    ring

lemma vol_part (p p1 q : ℝ) :
    (volume {v | v ∈ Icc (0 : ℝ) 1 ∧ (prof P p).buy p1 v = false ∧ q + P.c ≤ v}).toReal =
      max (min (W P p1) 1 - max 0 (q + P.c)) 0 := by
  apply vol_sandwich
  · intro v hv
    simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hv
    simp only [prof, mem_setOf_eq, mem_Icc, decide_eq_false_iff_not, not_le]
    exact ⟨⟨hv.1.1.le, hv.2.2.le⟩, hv.2.1, hv.1.2.le⟩
  · intro v hv
    simp only [prof, mem_setOf_eq, mem_Icc, decide_eq_false_iff_not, not_le] at hv
    simp only [mem_Icc, max_le_iff, le_min_iff]
    exact ⟨⟨hv.1.1, hv.2.2⟩, hv.2.1.le, hv.1.2⟩

lemma profit2_eq (hS : P.Standing) (hA : P.Assumption1) (p p1 q : ℝ) :
    profit2 P (prof P p) p1 q = k1 P * ((1 - (min (max 0 (W P p1)) 1) ^ 2) / 2) +
      q * max (min (W P p1) 1 - max 0 (q + P.c)) 0 := by
  unfold profit2
  rw [int_part P hS hA, vol_part]

lemma profit_eq (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) :
    profit P (prof P p) p1 = p1 * max (1 - max 0 (W P p1)) 0 +
      P.d * (k1 P * ((1 - (min (max 0 (W P p1)) 1) ^ 2) / 2) +
        Q P p1 * max (min (W P p1) 1 - max 0 (Q P p1 + P.c)) 0) := by
  unfold profit
  rw [buyer_set, Real.volume_Icc, ENNReal.toReal_ofReal', profit2_eq P hS hA]
  rfl

lemma minW_le_c (hS : P.Standing) (hA : P.Assumption1) (p1 : ℝ) (hB : p1 < ps P ∨ 1 ≤ P.c) :
    min (max 0 (W P p1)) 1 ≤ P.c := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, -⟩ := pos P hS hA
  rcases hB with h | h
  · have hW : W P p1 = wB P p1 := if_pos (Or.inl h)
    rw [hW]
    refine (min_le_left _ _).trans (max_le hc ?_)
    unfold wB; rw [div_le_iff₀ hbt]; unfold ps at h; unfold bt; nlinarith
  · exact (min_le_right _ _).trans h

lemma p2_opt (hS : P.Standing) (hA : P.Assumption1) (p p1 q : ℝ) :
    profit2 P (prof P p) p1 q ≤ profit2 P (prof P p) p1 ((prof P p).p2 p1) := by
  show _ ≤ profit2 P (prof P p) p1 (Q P p1)
  rw [profit2_eq P hS hA, profit2_eq P hS hA]
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  suffices q * max (min (W P p1) 1 - max 0 (q + P.c)) 0 ≤
      Q P p1 * max (min (W P p1) 1 - max 0 (Q P p1 + P.c)) 0 by linarith
  by_cases hB : p1 < ps P ∨ 1 ≤ P.c
  · have hQ : Q P p1 = 1 := if_pos hB
    have hm : min (W P p1) 1 ≤ P.c := by
      have := minW_le_c P hS hA p1 hB
      rcases le_total 0 (W P p1) with h | h
      · rwa [max_eq_right h] at this
      · exact (min_le_left _ _).trans (h.trans hc)
    have hz : min (W P p1) 1 - max 0 (1 + P.c) ≤ 0 := by
      linarith [min_le_right (W P p1) 1, le_max_right 0 (1 + P.c)]
    rw [hQ, max_eq_right hz, mul_zero]
    rcases le_or_gt q 0 with hq | hq
    · exact mul_nonpos_of_nonpos_of_nonneg hq (le_max_right _ _)
    · rw [max_eq_right (by linarith [le_max_right 0 (q + P.c)]), mul_zero]
  · have hW : W P p1 = wA P p1 := if_neg hB
    have hQ : Q P p1 = (min (wA P p1) 1 - P.c) / 2 := if_neg hB
    have hps : ps P ≤ p1 := not_lt.1 (not_or.1 hB).1
    have hc1 : P.c < 1 := not_le.1 (not_or.1 hB).2
    have hwc := wA_ge_c P hS hA hps
    have hcm : P.c ≤ min (wA P p1) 1 := le_min hwc hc1.le
    rw [hQ, hW]
    generalize min (wA P p1) 1 = m at hcm ⊢
    rw [max_eq_right (by linarith : (0:ℝ) ≤ (m - P.c) / 2 + P.c),
      max_eq_left (by linarith : (0:ℝ) ≤ m - ((m - P.c) / 2 + P.c))]
    rcases le_or_gt q 0 with hq | hq
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hq (le_max_right (m - max 0 (q + P.c)) 0)]
    · rw [max_eq_right (by linarith : (0:ℝ) ≤ q + P.c)]
      rcases le_total (m - (q + P.c)) 0 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith [sq_nonneg (m - P.c - 2 * q)]

lemma profit_B (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) (hB : p1 < ps P ∨ 1 ≤ P.c) :
    profit P (prof P p) p1 = p1 * max (1 - max 0 (wB P p1)) 0 +
      P.d * (k1 P * ((1 - (min (max 0 (wB P p1)) 1) ^ 2) / 2)) := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  rw [profit_eq P hS hA]
  have hW : W P p1 = wB P p1 := if_pos hB
  have hQ : Q P p1 = 1 := if_pos hB
  have hz : min (W P p1) 1 - max 0 (1 + P.c) ≤ 0 := by
    linarith [min_le_right (W P p1) 1, le_max_right 0 (1 + P.c)]
  rw [hQ, max_eq_right hz, hW]
  ring

lemma bound_B (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) (hB : p1 < ps P ∨ 1 ≤ P.c) :
    profit P (prof P p) p1 ≤ PiB P (min (max 0 (wB P p1)) 1) := by
  obtain ⟨hal, hbt, -⟩ := pos P hS hA
  rw [profit_B P hS hA p p1 hB]
  have key : wB P p1 * bt P = p1 + P.c * (1 + P.d) := by
    unfold wB; exact div_mul_cancel₀ _ hbt.ne'
  unfold PiB
  generalize wB P p1 = w at key ⊢
  have hp1 : p1 = w * bt P - P.c * (1 + P.d) := by linarith
  subst hp1
  rcases le_total w 0 with h0 | h0
  · rw [max_eq_left h0, min_eq_left zero_le_one, sub_zero, max_eq_left zero_le_one]
    nlinarith [mul_nonneg (neg_nonneg.2 h0) hbt.le]
  · rw [max_eq_right h0]
    rcases le_total w 1 with h1 | h1
    · rw [min_eq_left h1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - w)]
      apply le_of_eq; ring
    · rw [min_eq_right h1, max_eq_right (by linarith : 1 - w ≤ 0)]
      apply le_of_eq; ring

lemma exact_B (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) (hB : p1 < ps P ∨ 1 ≤ P.c)
    (h0 : 0 ≤ wB P p1) (h1 : wB P p1 ≤ 1) :
    profit P (prof P p) p1 = PiB P (wB P p1) := by
  obtain ⟨hal, hbt, -⟩ := pos P hS hA
  rw [profit_B P hS hA p p1 hB]
  have key : wB P p1 * bt P = p1 + P.c * (1 + P.d) := by
    unfold wB; exact div_mul_cancel₀ _ hbt.ne'
  unfold PiB
  generalize wB P p1 = w at key h0 h1 ⊢
  have hp1 : p1 = w * bt P - P.c * (1 + P.d) := by linarith
  subst hp1
  rw [max_eq_right h0, min_eq_left h1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - w)]
  ring

lemma profit_A (hS : P.Standing) (hA : P.Assumption1) (p p1 : ℝ) (hB : ¬ (p1 < ps P ∨ 1 ≤ P.c)) :
    profit P (prof P p) p1 = PiA P (min (wA P p1) 1) := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, -⟩ := pos P hS hA
  rw [profit_eq P hS hA]
  have hW : W P p1 = wA P p1 := if_neg hB
  have hQ : Q P p1 = (min (wA P p1) 1 - P.c) / 2 := if_neg hB
  have hps : ps P ≤ p1 := not_lt.1 (not_or.1 hB).1
  have hc1 : P.c < 1 := not_le.1 (not_or.1 hB).2
  have hwc := wA_ge_c P hS hA hps
  have key : wA P p1 * al P = p1 + P.c * (1 + P.d / 2) := by
    unfold wA; exact div_mul_cancel₀ _ hal.ne'
  rw [hQ, hW, max_eq_right (hc.trans hwc)]
  unfold PiA
  generalize wA P p1 = w at key hwc ⊢
  have hp1 : p1 = w * al P - P.c * (1 + P.d / 2) := by linarith
  subst hp1
  rcases le_total w 1 with h1 | h1
  · rw [min_eq_left h1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - w),
      max_eq_right (by linarith : (0:ℝ) ≤ (w - P.c) / 2 + P.c),
      max_eq_left (by linarith : (0:ℝ) ≤ w - ((w - P.c) / 2 + P.c))]
    ring
  · rw [min_eq_right h1, max_eq_right (by linarith : 1 - w ≤ 0),
      max_eq_right (by linarith : (0:ℝ) ≤ (1 - P.c) / 2 + P.c),
      max_eq_left (by linarith : (0:ℝ) ≤ 1 - ((1 - P.c) / 2 + P.c))]
    ring

/-! ### quadratic algebra -/

lemma PiA_diff (m n : ℝ) : PiA P m - PiA P n = (m - n) * ((al P + P.c) - E P / 4 * (m + n)) := by
  unfold PiA al E k1; ring

lemma PiB_diff (m n : ℝ) : PiB P m - PiB P n =
    (m - n) * ((bt P + P.c * (1 + P.d)) - (2 + P.d + P.d * P.mu + P.d * P.sigma) / 2 * (m + n)) := by
  unfold PiB bt k1; ring

lemma PiA_c : PiA P P.c = PiB P P.c := by unfold PiA PiB al bt k1; ring

lemma vbE (hS : P.Standing) (hA : P.Assumption1) : vb P * E P = 2 * (al P + P.c) := by
  obtain ⟨-, -, hE, -⟩ := pos P hS hA
  unfold vb; exact div_mul_cancel₀ _ hE.ne'

lemma XD (hS : P.Standing) (hA : P.Assumption1) :
    X P * (2 + P.d + P.d * P.mu + P.d * P.sigma) = bt P + P.c * (1 + P.d) := by
  obtain ⟨-, -, -, hD, -⟩ := pos P hS hA
  unfold X; rw [div_mul_cancel₀ _ hD.ne']; unfold bt; ring

lemma PiA_le_vb (hS : P.Standing) (hA : P.Assumption1) (m : ℝ) : PiA P m ≤ PiA P (vb P) := by
  obtain ⟨-, -, hE, -⟩ := pos P hS hA
  have h1 : al P + P.c = E P / 4 * (2 * vb P) := by linarith [vbE P hS hA]
  have h2 : PiA P m - PiA P (vb P) = -(E P / 4) * (m - vb P) ^ 2 := by
    rw [PiA_diff, h1]; ring
  nlinarith [mul_nonneg hE.le (sq_nonneg (m - vb P))]

lemma PiA_le_c (hS : P.Standing) (hA : P.Assumption1) {m : ℝ} (h1 : vb P ≤ P.c) (h2 : P.c ≤ m) :
    PiA P m ≤ PiA P P.c := by
  obtain ⟨-, -, hE, -⟩ := pos P hS hA
  have hv := vbE P hS hA
  have hf : al P + P.c - E P / 4 * (m + P.c) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hE.le, mul_le_mul_of_nonneg_left h2 hE.le]
  have := mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hf)
  have hd := PiA_diff P m P.c
  nlinarith

lemma PiB_le_X (hS : P.Standing) (hA : P.Assumption1) (m : ℝ) : PiB P m ≤ PiB P (X P) := by
  obtain ⟨-, -, -, hD, -⟩ := pos P hS hA
  have h1 := XD P hS hA
  have h2 : PiB P m - PiB P (X P) =
      -((2 + P.d + P.d * P.mu + P.d * P.sigma) / 2) * (m - X P) ^ 2 := by
    rw [PiB_diff, ← h1]; ring
  nlinarith [mul_nonneg hD.le (sq_nonneg (m - X P))]

lemma PiB_le_c (hS : P.Standing) (hA : P.Assumption1) {m : ℝ} (h1 : m ≤ P.c) (h2 : P.c ≤ X P) :
    PiB P m ≤ PiB P P.c := by
  obtain ⟨-, -, -, hD, -⟩ := pos P hS hA
  have hx := XD P hS hA
  have hf : 0 ≤ bt P + P.c * (1 + P.d) - (2 + P.d + P.d * P.mu + P.d * P.sigma) / 2 * (m + P.c) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hD.le, mul_le_mul_of_nonneg_left h2 hD.le]
  have := mul_nonneg (sub_nonneg.2 h1) hf
  have hd := PiB_diff P m P.c
  nlinarith

lemma PiB_le_v2 (hS : P.Standing) (hA : P.Assumption1) {m : ℝ} (h1 : m ≤ P.c) :
    PiB P m ≤ PiB P (min (X P) P.c) := by
  rcases le_total (X P) P.c with h | h
  · rw [min_eq_left h]; exact PiB_le_X P hS hA m
  · rw [min_eq_right h]; exact PiB_le_c P hS hA h1 h

lemma PiB_nonpos (hS : P.Standing) (hA : P.Assumption1) (hT : T2 P ≤ P.c) {m : ℝ}
    (h0 : 0 ≤ m) (h1 : m ≤ 1) : PiB P m ≤ 0 := by
  obtain ⟨hd, hd1, hc, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨-, -, -, -, -, -, hmu, hds, hdm⟩ := pos P hS hA
  have hT' : 1 + P.d + P.d * P.mu ≤ P.c * (1 + P.d) := by
    unfold T2 at hT
    have e : P.d / (1 + P.d) * P.mu * (1 + P.d) = P.d * P.mu := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hT (by linarith : (0:ℝ) ≤ 1 + P.d)]
  have hcoef : 0 ≤ 1 + P.d * P.sigma + P.d * (1 + P.mu - P.sigma) / 2 := by nlinarith
  have hBn : (1 + P.d * P.sigma) * m - P.c * (1 + P.d) + P.d * (1 + P.mu - P.sigma) * (1 + m) / 2 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hcoef]
  have e : PiB P m = (1 - m) * ((1 + P.d * P.sigma) * m - P.c * (1 + P.d) +
      P.d * (1 + P.mu - P.sigma) * (1 + m) / 2) := by unfold PiB bt k1; ring
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 hBn)]

/-! ### thresholds -/

lemma T1_lt_one (hS : P.Standing) (hA : P.Assumption1) : T1 P < 1 := by
  obtain ⟨-, -, -, -, hE1, -, -, -, hdm⟩ := pos P hS hA
  unfold T1; rw [div_lt_iff₀ hE1]; linarith

lemma vb_ge_c (hS : P.Standing) (hA : P.Assumption1) (h : P.c ≤ T1 P) : P.c ≤ vb P := by
  obtain ⟨-, -, hE, -, hE1, -⟩ := pos P hS hA
  unfold T1 at h; rw [le_div_iff₀ hE1] at h
  unfold vb; rw [le_div_iff₀ hE]; unfold al E; linarith

lemma vb_le_c (hS : P.Standing) (hA : P.Assumption1) (h : T1 P < P.c) : vb P ≤ P.c := by
  obtain ⟨-, -, hE, -, hE1, -⟩ := pos P hS hA
  unfold T1 at h; rw [div_lt_iff₀ hE1] at h
  unfold vb; rw [div_le_iff₀ hE]; unfold al E; linarith

lemma vb_le_one (hS : P.Standing) (hA : P.Assumption1) (h : P.c ≤ 1) : vb P ≤ 1 := by
  obtain ⟨-, -, hE, -, -, -, -, -, hdm⟩ := pos P hS hA
  unfold vb; rw [div_le_iff₀ hE]; unfold al E; linarith

lemma c_le_X (hS : P.Standing) (hA : P.Assumption1) (h : P.c ≤ T1 P) : P.c ≤ X P := by
  obtain ⟨hd, hd1, hc, -⟩ := basics P hS hA
  obtain ⟨-, -, -, hD, hE1, -⟩ := pos P hS hA
  have hc1 : P.c < 1 := lt_of_le_of_lt h (T1_lt_one P hS hA)
  unfold T1 at h; rw [le_div_iff₀ hE1] at h
  unfold X; rw [le_div_iff₀ hD]
  nlinarith [mul_nonneg hd.le (by linarith : (0:ℝ) ≤ 1 - P.c)]

lemma X_lt_one (hS : P.Standing) (hA : P.Assumption1) (h : P.c < T2 P) : X P < 1 := by
  obtain ⟨hd, hd1, hc, -⟩ := basics P hS hA
  obtain ⟨-, -, -, hD, -⟩ := pos P hS hA
  have hT' : P.c * (1 + P.d) < 1 + P.d + P.d * P.mu := by
    unfold T2 at h
    have e : P.d / (1 + P.d) * P.mu * (1 + P.d) = P.d * P.mu := by field_simp
    nlinarith [mul_lt_mul_of_pos_right h (by linarith : (0:ℝ) < 1 + P.d)]
  unfold X; rw [div_lt_iff₀ hD]; linarith

lemma X_pos (hS : P.Standing) (hA : P.Assumption1) : 0 < X P := by
  obtain ⟨hd, hd1, hc, -⟩ := basics P hS hA
  obtain ⟨-, -, -, hD, -, -, -, hds, -⟩ := pos P hS hA
  unfold X; apply div_pos _ hD; nlinarith

lemma wA_ps (hS : P.Standing) (hA : P.Assumption1) : wA P (ps P) = P.c := by
  obtain ⟨hal, -⟩ := pos P hS hA
  unfold wA; rw [div_eq_iff hal.ne']; unfold ps al; ring

lemma wB_ps (hS : P.Standing) (hA : P.Assumption1) : wB P (ps P) = P.c := by
  obtain ⟨-, hbt, -⟩ := pos P hS hA
  unfold wB; rw [div_eq_iff hbt.ne']; unfold ps bt; ring

lemma P1B_eq (hS : P.Standing) (hA : P.Assumption1) :
    P1B P = al P * vb P - P.c * (1 + P.d / 2) := by
  obtain ⟨-, -, hE, -⟩ := pos P hS hA
  have hE' : 4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma ≠ 0 := hE.ne'
  unfold P1B vb al E
  field_simp
  ring

lemma P2B_eq (hS : P.Standing) (hA : P.Assumption1) :
    P2B P = bt P * v2B P - P.c * (1 + P.d) := by
  obtain ⟨-, hbt, -, hD, -⟩ := pos P hS hA
  have hD' : 2 + P.d + P.d * P.mu + P.d * P.sigma ≠ 0 := hD.ne'
  have hY : ((1 + P.d * P.sigma) ^ 2 - (1 + P.d) * (1 + P.d + P.d * P.mu) * P.c)
      / (2 + P.d + P.d * P.mu + P.d * P.sigma) = bt P * X P - P.c * (1 + P.d) := by
    unfold X bt; field_simp; ring
  have hps : P.d * (P.sigma - 1) * P.c = bt P * P.c - P.c * (1 + P.d) := by unfold bt; ring
  unfold P2B
  rw [hY, hps]
  show _ = bt P * min (X P) P.c - _
  rcases le_total (X P) P.c with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith [mul_le_mul_of_nonneg_left h hbt.le])]
  · rw [min_eq_right h, min_eq_right (by nlinarith [mul_le_mul_of_nonneg_left h hbt.le])]

lemma equil (hS : P.Standing) (hA : P.Assumption1) (p : ℝ)
    (hmax : ∀ p1, profit P (prof P p) p1 ≤ profit P (prof P p) p) : IsEquilibrium P (prof P p) :=
  ⟨fun _ hv ρ => RB_opt P hS hA hv.1 ρ, fun p1 q => p2_opt P hS hA p p1 q,
    fun p1 v hv => cons P hS hA p p1 v hv, hmax⟩

lemma clamp_nonneg (w : ℝ) : 0 ≤ min (max 0 w) 1 := le_min (le_max_left _ _) zero_le_one

/-! ### the three regimes -/

lemma partA (hS : P.Standing) (hA : P.Assumption1) (hc : P.c ≤ T1 P) :
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P1B P ∧ σ.p2 σ.p1 = p2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (vbar1B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (vlow1B P ≤ v → v < vbar1B P →
            σ.buy σ.p1 v = false ∧ σ.p2 σ.p1 + P.c ≤ v) ∧
          (v < vlow1B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c) := by
  obtain ⟨hd, hd1, hc0, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, hE, -⟩ := pos P hS hA
  have hc1 : P.c < 1 := lt_of_le_of_lt hc (T1_lt_one P hS hA)
  have hvbc := vb_ge_c P hS hA hc
  have hvb1 := vb_le_one P hS hA hc1.le
  have hcX := c_le_X P hS hA hc
  have hP1 := P1B_eq P hS hA
  have hnB : ¬ (P1B P < ps P ∨ 1 ≤ P.c) := by
    rintro (h | h)
    · rw [hP1] at h; unfold ps al at h; unfold al at hal
      nlinarith [mul_nonneg hal.le (sub_nonneg.2 hvbc)]
    · linarith
  have hwA : wA P (P1B P) = vb P := by
    unfold wA; rw [hP1, div_eq_iff hal.ne']; ring
  have hvbar : vbar1B P = vb P := by
    have h2 : (2 - P.d + 2 * P.d * P.sigma) ≠ 0 := by unfold al at hal; linarith
    unfold vbar1B; rw [hP1, div_eq_iff h2]; unfold al; ring
  have hp2B : p2B P = (vb P - P.c) / 2 := by
    have h2 : (2 - P.d + 2 * P.d * P.sigma) ≠ 0 := by unfold al at hal; linarith
    unfold p2B; rw [hP1, div_eq_iff h2]; unfold al; ring
  have hW : W P (P1B P) = vb P := by
    rw [show W P (P1B P) = wA P (P1B P) from if_neg hnB, hwA]
  have hQ : Q P (P1B P) = p2B P := by
    rw [show Q P (P1B P) = (min (wA P (P1B P)) 1 - P.c) / 2 from if_neg hnB, hwA,
      min_eq_left hvb1, hp2B]
  refine ⟨prof P (P1B P), equil P hS hA _ ?_, rfl, hQ, ?_⟩
  · intro p1
    rw [profit_A P hS hA _ _ hnB, hwA, min_eq_left hvb1]
    by_cases hB : p1 < ps P ∨ 1 ≤ P.c
    · refine (bound_B P hS hA _ p1 hB).trans ?_
      have hm : min (max 0 (wB P p1)) 1 ≤ P.c := by
        have := minW_le_c P hS hA p1 hB
        rwa [show W P p1 = wB P p1 from if_pos hB] at this
      refine (PiB_le_c P hS hA hm hcX).trans ?_
      rw [← PiA_c]; exact PiA_le_vb P hS hA _
    · rw [profit_A P hS hA _ _ hB]; exact PiA_le_vb P hS hA _
  · intro v hv
    have hbuy : (prof P (P1B P)).buy (prof P (P1B P)).p1 v = decide (vb P ≤ v) := by
      show decide (W P (P1B P) ≤ v) = _
      rw [hW]
    have hp2 : (prof P (P1B P)).p2 (prof P (P1B P)).p1 = p2B P := hQ
    have hr := r_bounds P hS hA hv.1
    rw [hbuy, hp2, hvbar]
    refine ⟨fun h => ⟨decide_eq_true h, rfl, hr.1, hr.2⟩, fun h1 h2 => ⟨decide_eq_false (not_le.2 h2), ?_⟩,
      fun h => ⟨decide_eq_false (not_le.2 ?_), ?_⟩⟩
    · unfold vlow1B at h1; exact h1
    · unfold vlow1B at h; rw [hp2B] at h; linarith
    · unfold vlow1B at h; exact h

lemma partB (hS : P.Standing) (hA : P.Assumption1) (hc1 : T1 P < P.c) (hc2 : P.c < T2 P) :
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (v2B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (v < v2B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c) := by
  obtain ⟨hd, hd1, hc0, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, hE, -⟩ := pos P hS hA
  have hvbc := vb_le_c P hS hA hc1
  have hX1 := X_lt_one P hS hA hc2
  have hX0 := X_pos P hS hA
  have hv2 : v2B P = min (X P) P.c := rfl
  have hv20 : 0 ≤ v2B P := by rw [hv2]; exact le_min hX0.le hc0
  have hv21 : v2B P < 1 := by rw [hv2]; exact lt_of_le_of_lt (min_le_left _ _) hX1
  have hv2c : v2B P ≤ P.c := by rw [hv2]; exact min_le_right _ _
  have hP2 := P2B_eq P hS hA
  have hwB : wB P (P2B P) = v2B P := by
    unfold wB; rw [hP2, div_eq_iff hbt.ne']; ring
  have hP2ps : P2B P ≤ ps P := by
    have : P.d * (P.sigma - 1) * P.c = ps P := by unfold ps; ring
    unfold P2B; rw [this]; exact min_le_right _ _
  -- on-path facts
  have hon : W P (P2B P) = v2B P ∧ profit P (prof P (P2B P)) (P2B P) = PiB P (v2B P) ∧
      (P2B P < ps P ∨ 1 ≤ P.c → Q P (P2B P) = 1) ∧
      (¬ (P2B P < ps P ∨ 1 ≤ P.c) → Q P (P2B P) = 0 ∧ v2B P = P.c) := by
    by_cases hB : P2B P < ps P ∨ 1 ≤ P.c
    · refine ⟨by rw [show W P (P2B P) = wB P (P2B P) from if_pos hB, hwB], ?_,
        fun _ => if_pos hB, fun h => absurd hB h⟩
      rw [exact_B P hS hA _ _ hB (by rw [hwB]; exact hv20) (by rw [hwB]; exact hv21.le), hwB]
    · have hps : ps P ≤ P2B P := not_lt.1 (not_or.1 hB).1
      have hcl : P.c < 1 := not_le.1 (not_or.1 hB).2
      have he : P2B P = ps P := le_antisymm hP2ps hps
      have hvc : v2B P = P.c := by
        have h' : bt P * v2B P = bt P * P.c := by
          have : ps P = bt P * P.c - P.c * (1 + P.d) := by unfold ps bt; ring
          linarith
        exact mul_left_cancel₀ hbt.ne' h'
      have hwa : wA P (P2B P) = P.c := by rw [he, wA_ps P hS hA]
      refine ⟨by rw [show W P (P2B P) = wA P (P2B P) from if_neg hB, hwa, hvc], ?_,
        fun h => absurd h hB, fun _ => ⟨?_, hvc⟩⟩
      · rw [profit_A P hS hA _ _ hB, hwa, min_eq_left hcl.le, PiA_c, hvc]
      · rw [show Q P (P2B P) = (min (wA P (P2B P)) 1 - P.c) / 2 from if_neg hB, hwa,
          min_eq_left hcl.le]; ring
  obtain ⟨hW, hprof, hQ1, hQ2⟩ := hon
  refine ⟨prof P (P2B P), equil P hS hA _ ?_, rfl, ?_⟩
  · intro p1
    rw [hprof]
    by_cases hB : p1 < ps P ∨ 1 ≤ P.c
    · refine (bound_B P hS hA _ p1 hB).trans ?_
      have hm : min (max 0 (wB P p1)) 1 ≤ P.c := by
        have := minW_le_c P hS hA p1 hB
        rwa [show W P p1 = wB P p1 from if_pos hB] at this
      rw [hv2]; exact PiB_le_v2 P hS hA hm
    · rw [profit_A P hS hA _ _ hB]
      have hps : ps P ≤ p1 := not_lt.1 (not_or.1 hB).1
      have hcl : P.c < 1 := not_le.1 (not_or.1 hB).2
      have hcm : P.c ≤ min (wA P p1) 1 := le_min (wA_ge_c P hS hA hps) hcl.le
      refine (PiA_le_c P hS hA hvbc hcm).trans ?_
      rw [PiA_c, hv2]; exact PiB_le_v2 P hS hA le_rfl
  · intro v hv
    have hbuy : (prof P (P2B P)).buy (prof P (P2B P)).p1 v = decide (v2B P ≤ v) := by
      show decide (W P (P2B P) ≤ v) = _
      rw [hW]
    have hr := r_bounds P hS hA hv.1
    rw [hbuy]
    refine ⟨fun h => ⟨decide_eq_true h, rfl, hr.1, hr.2⟩, fun h => ⟨decide_eq_false (not_le.2 h), ?_⟩⟩
    show v < Q P (P2B P) + P.c
    by_cases hB : P2B P < ps P ∨ 1 ≤ P.c
    · rw [hQ1 hB]; linarith
    · obtain ⟨hq, hvc⟩ := hQ2 hB
      rw [hq]; linarith

lemma partC (hS : P.Standing) (hA : P.Assumption1) (hc : T2 P ≤ P.c) :
      ∃ σ : Profile, IsEquilibrium P σ ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1, σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c := by
  obtain ⟨hd, hd1, hc0, hs, hkL, hkH, hA1, hA2⟩ := basics P hS hA
  obtain ⟨hal, hbt, hE, -, -, -, hmu, hds, hdm⟩ := pos P hS hA
  have hT2 : 1 < T2 P := by
    unfold T2
    have : 0 < P.d / (1 + P.d) * P.mu := mul_pos (div_pos hd (by linarith)) hmu
    linarith
  have hc1 : 1 < P.c := lt_of_lt_of_le hT2 hc
  have hB : ∀ p1 : ℝ, p1 < ps P ∨ 1 ≤ P.c := fun _ => Or.inr hc1.le
  have hW : W P (ps P) = P.c := by
    rw [show W P (ps P) = wB P (ps P) from if_pos (hB _), wB_ps P hS hA]
  refine ⟨prof P (ps P), equil P hS hA _ ?_, ?_⟩
  · intro p1
    have h0 : profit P (prof P (ps P)) (ps P) = 0 := by
      rw [profit_B P hS hA _ _ (hB _), wB_ps P hS hA, max_eq_right hc0,
        max_eq_right (by linarith : 1 - P.c ≤ 0), min_eq_right hc1.le]
      ring
    rw [h0]
    refine (bound_B P hS hA _ p1 (hB p1)).trans ?_
    exact PiB_nonpos P hS hA hc (clamp_nonneg _) (min_le_right _ _)
  · intro v hv
    refine ⟨?_, ?_⟩
    · show decide (W P (ps P) ≤ v) = false
      rw [hW]; exact decide_eq_false (not_le.2 (by linarith [hv.2]))
    · show v < Q P (ps P) + P.c
      rw [show Q P (ps P) = 1 from if_pos (hB _)]; linarith [hv.2]

end GDPRB2

open GDPRDataMarkets.Benchmark in
theorem solution (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.c ≤ T1 P →
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P1B P ∧ σ.p2 σ.p1 = p2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (vbar1B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (vlow1B P ≤ v → v < vbar1B P →
            σ.buy σ.p1 v = false ∧ σ.p2 σ.p1 + P.c ≤ v) ∧
          (v < vlow1B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c)) ∧
    (T1 P < P.c → P.c < T2 P →
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (v2B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (v < v2B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c)) ∧
    (T2 P ≤ P.c →
      ∃ σ : Profile, IsEquilibrium P σ ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1, σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c) := by
  exact ⟨GDPRB2.partA P hS hA, GDPRB2.partB P hS hA, GDPRB2.partC P hS hA⟩
