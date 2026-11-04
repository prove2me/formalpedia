-- Prove2me | solution 1 for BBDisclosure.Stage2.uniform_eq_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T15:16:24.197881+00:00
-- url     : https://prove2.me/submissions/e331ec2e-838e-4841-977f-2e9d1a206a13

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model
import Theorems.Thm_BBDisclosure_Stage2_lemma_2_region_1

open BBDisclosure.Stage2


namespace BBDSolInt

noncomputable def ind (h q : ℝ) : ℝ := if h < q then 1 else 0

lemma bel_mono {h : ℝ} (h0 : 0 ≤ h) : Monotone (bel h) := by
  intro x y hxy
  unfold bel
  split_ifs <;> linarith

lemma bel_nonneg {h q : ℝ} (h0 : 0 ≤ h) : 0 ≤ bel h q := by
  unfold bel; split_ifs <;> linarith

lemma bel_sq_mono {h : ℝ} (h0 : 0 ≤ h) : Monotone (fun q => bel h q ^ 2) := by
  intro x y hxy
  have := bel_mono h0 hxy
  have := bel_nonneg (q := x) h0
  dsimp; nlinarith

lemma ind_mono (h : ℝ) : Monotone (ind h) := by
  intro x y hxy; unfold ind; split_ifs <;> linarith

lemma ii_bel (h : ℝ) (h0 : 0 ≤ h) : IntervalIntegrable (bel h) MeasureTheory.volume 0 1 :=
  (bel_mono h0).intervalIntegrable
lemma ii_bel2 (h : ℝ) (h0 : 0 ≤ h) :
    IntervalIntegrable (fun q => bel h q ^ 2) MeasureTheory.volume 0 1 :=
  (bel_sq_mono h0).intervalIntegrable
lemma ii_ind (h : ℝ) : IntervalIntegrable (ind h) MeasureTheory.volume 0 1 :=
  (ind_mono h).intervalIntegrable

/-- split an ite integral at the threshold. -/
lemma split_ite (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (F : ℝ → ℝ) (G : ℝ)
    (hF : Continuous F) :
    ∫ q in (0:ℝ)..1, (if h < q then F q else G) = h * G + ∫ q in h..1, F q := by
  have hA : IntervalIntegrable (fun q => if h < q then F q else G) MeasureTheory.volume 0 h := by
    have : IntervalIntegrable (fun _ : ℝ => G) MeasureTheory.volume 0 h := intervalIntegrable_const
    refine this.congr ?_
    rw [Set.uIoc_of_le h0]
    intro q hq
    simp [not_lt.mpr hq.2]
  have hB : IntervalIntegrable (fun q => if h < q then F q else G) MeasureTheory.volume h 1 := by
    have : IntervalIntegrable F MeasureTheory.volume h 1 := hF.intervalIntegrable _ _
    refine this.congr ?_
    rw [Set.uIoc_of_le h1]
    intro q hq
    simp [hq.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB]
  congr 1
  · rw [intervalIntegral.integral_congr_ae (g := fun _ => G)]
    · simp
    · refine Filter.Eventually.of_forall (fun q hq => ?_)
      rw [Set.uIoc_of_le h0] at hq
      simp [not_lt.mpr hq.2]
  · apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun q hq => ?_)
    rw [Set.uIoc_of_le h1] at hq
    simp [hq.1]

lemma int_bel (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : ∫ q in (0:ℝ)..1, bel h q = 1 / 2 := by
  have := split_ite h h0 h1 (fun q => q) (h / 2) continuous_id
  simp only [bel] at *
  rw [this, integral_id]; ring

lemma int_bel2 (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ∫ q in (0:ℝ)..1, bel h q ^ 2 = 1 / 3 - h ^ 3 / 12 := by
  have := split_ite h h0 h1 (fun q => q ^ 2) ((h / 2) ^ 2) (continuous_pow 2)
  have e : (fun q => bel h q ^ 2) = fun q => if h < q then q ^ 2 else (h / 2) ^ 2 := by
    funext q; unfold bel; split_ifs <;> rfl
  rw [e, this, integral_pow]; ring

lemma int_ind (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : ∫ q in (0:ℝ)..1, ind h q = 1 - h := by
  have := split_ite h h0 h1 (fun _ => 1) 0 continuous_const
  simp only [ind] at *
  rw [this]; simp

/-- master moment lemma with two thresholds. -/
lemma moment (h1 h2 : ℝ) (h10 : 0 ≤ h1) (h11 : h1 ≤ 1) (h20 : 0 ≤ h2) (h21 : h2 ≤ 1)
    (α β1 γ1 δ1 β2 γ2 δ2 : ℝ) :
    ∫ q in (0:ℝ)..1, (α + β1 * bel h1 q + γ1 * bel h1 q ^ 2 + δ1 * ind h1 q
        + β2 * bel h2 q + γ2 * bel h2 q ^ 2 + δ2 * ind h2 q) =
      α + β1 / 2 + γ1 * (1 / 3 - h1 ^ 3 / 12) + δ1 * (1 - h1)
        + β2 / 2 + γ2 * (1 / 3 - h2 ^ 3 / 12) + δ2 * (1 - h2) := by
  have i1 := (ii_bel h1 h10).const_mul β1
  have i2 := (ii_bel2 h1 h10).const_mul γ1
  have i3 := (ii_ind h1).const_mul δ1
  have i4 := (ii_bel h2 h20).const_mul β2
  have i5 := (ii_bel2 h2 h20).const_mul γ2
  have i6 := (ii_ind h2).const_mul δ2
  have i0 : IntervalIntegrable (fun _ : ℝ => α) MeasureTheory.volume 0 1 := intervalIntegrable_const
  rw [intervalIntegral.integral_add (((((i0.add i1).add i2).add i3).add i4).add i5) i6,
    intervalIntegral.integral_add ((((i0.add i1).add i2).add i3).add i4) i5,
    intervalIntegral.integral_add (((i0.add i1).add i2).add i3) i4,
    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  rw [int_bel h1 h10 h11, int_bel2 h1 h10 h11, int_ind h1 h10 h11,
    int_bel h2 h20 h21, int_bel2 h2 h20 h21, int_ind h2 h20 h21]
  simp; ring

end BBDSolInt



namespace BBDSolNash
open BBDSolInt

lemma nashA_bdry (p : ℝ × ℝ) : IsTurfNashA (1/2) 1 0 p ↔ p = (1, 0) := by
  obtain ⟨a, s⟩ := p
  simp only [IsTurfNashA, revAturfA, revBturfA, xaTurf, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hs, hA, hB⟩
    have k := hA (1 + s) (by linarith)
    have e1 : min (1/2 : ℝ) (max 0 ((1 + s - (1 + s) + 1 - 0) / 2)) = 1/2 := by
      rw [max_eq_right (by norm_num)]; norm_num
    rw [e1] at k
    have hap : a = 1 + s := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : min (1/2 : ℝ) (max 0 ((1 + s - a + 1 - 0) / 2)) = 1/2 := by
          rw [max_eq_right (by linarith), min_eq_left (by linarith)]
        rw [this] at k; linarith
      · rcases le_total ((1 + s - a + 1 - 0) / 2) 0 with h0 | h0
        · rw [max_eq_left h0, min_eq_right (by norm_num)] at k; nlinarith
        · rw [max_eq_right h0, min_eq_right (by linarith)] at k; nlinarith
    subst hap
    have hs00 : s = 0 := by
      by_contra hne
      have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hne)
      have k2 := hB (s / 2) (by linarith)
      have e2 : min (1/2 : ℝ) (max 0 ((1 + s - (1 + s) + 1 - 0) / 2)) = 1/2 := by
        rw [max_eq_right (by norm_num)]; norm_num
      rw [e2] at k2
      rcases le_total ((1 + s / 2 - (1 + s) + 1 - 0) / 2) 0 with h0 | h0
      · rw [max_eq_left h0, min_eq_right (by norm_num)] at k2; nlinarith
      · rw [max_eq_right h0, min_eq_right (by linarith)] at k2; nlinarith
    subst hs00
    norm_num
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, le_refl _, ?_, ?_⟩
    · intro p' hp'
      have e1 : min (1/2 : ℝ) (max 0 ((1 + 0 - 1 + 1 - 0) / 2)) = 1/2 := by norm_num
      rw [e1]
      rcases le_total ((1 + 0 - p' + 1 - 0) / 2) 0 with h0 | h0
      · rw [max_eq_left h0, min_eq_right (by norm_num)]; linarith
      · rw [max_eq_right h0]
        rcases le_total (1/2 : ℝ) ((1 + 0 - p' + 1 - 0) / 2) with h1 | h1
        · rw [min_eq_left h1]; linarith
        · rw [min_eq_right h1]; nlinarith [sq_nonneg (p' - 1)]
    · intro p' hp'
      have e1 : min (1/2 : ℝ) (max 0 ((1 + p' - 1 + 1 - 0) / 2)) = 1/2 := by
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      rw [e1]; norm_num

lemma nashB_bdry (p : ℝ × ℝ) : IsTurfNashB (1/2) 0 1 p ↔ p = (0, 1) := by
  obtain ⟨s, a⟩ := p
  simp only [IsTurfNashB, revAturfB, revBturfB, xbTurf, Prod.mk.injEq]
  constructor
  · rintro ⟨hs, ha, hA, hB⟩
    have k := hB (1 + s) (by linarith)
    have e1 : min (1 : ℝ) (max (1/2) ((1 + (1 + s) - s + 0 - 1) / 2)) = 1/2 := by
      rw [max_eq_left (by linarith)]; norm_num
    rw [e1] at k
    have hap : a = 1 + s := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : min (1 : ℝ) (max (1/2) ((1 + a - s + 0 - 1) / 2)) = 1/2 := by
          rw [max_eq_left (by linarith), min_eq_right (by linarith)]
        rw [this] at k; linarith
      · rcases le_total ((1 + a - s + 0 - 1) / 2) 1 with h0 | h0
        · rw [max_eq_right (by linarith), min_eq_right h0] at k; nlinarith
        · rw [min_eq_left (le_trans h0 (le_max_right _ _))] at k; nlinarith
    subst hap
    have hs00 : s = 0 := by
      by_contra hne
      have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hne)
      have k2 := hA (s / 2) (by linarith)
      have e2 : min (1 : ℝ) (max (1/2) ((1 + (1 + s) - s + 0 - 1) / 2)) = 1/2 := by
        rw [max_eq_left (by linarith)]; norm_num
      rw [e2] at k2
      rcases le_total ((1 + (1 + s) - s / 2 + 0 - 1) / 2) 1 with h0 | h0
      · rw [max_eq_right (by linarith), min_eq_right h0] at k2; nlinarith
      · rw [min_eq_left (le_trans h0 (le_max_right _ _))] at k2; nlinarith
    subst hs00
    norm_num
  · rintro ⟨rfl, rfl⟩
    refine ⟨le_refl _, by norm_num, ?_, ?_⟩
    · intro p' hp'
      have e1 : min (1 : ℝ) (max (1/2) ((1 + 1 - p' + 0 - 1) / 2)) = 1/2 := by
        rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
      rw [e1]; norm_num
    · intro p' hp'
      have e1 : min (1 : ℝ) (max (1/2) ((1 + 1 - 0 + 0 - 1) / 2)) = 1/2 := by norm_num
      rw [e1]
      rcases le_total ((1 + p' - 0 + 0 - 1) / 2) 1 with h0 | h0
      · rw [min_eq_right (max_le (by norm_num) h0)]
        rcases le_total (1/2 : ℝ) ((1 + p' - 0 + 0 - 1) / 2) with h1 | h1
        · rw [max_eq_right h1]; nlinarith [sq_nonneg (p' - 1)]
        · rw [max_eq_left h1]; nlinarith
      · rw [min_eq_left (le_trans h0 (le_max_right _ _))]; nlinarith

/-- Full characterization of turf-A Nash equilibria at `x1 = 1/2`. -/
lemma nashA_iff (u w : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) (p : ℝ × ℝ) :
    IsTurfNashA (1/2) u w p ↔ p = ((2 + u - w) / 3, (1 + w - u) / 3) := by
  by_cases hb : u - w < 1
  · have := (lemma_2_region_1 (1/2) u w 0 0 hu hw ⟨le_refl _, by norm_num⟩
      ⟨le_refl _, by norm_num⟩ ⟨by linarith, by norm_num⟩).1 p
    rw [this]
    constructor <;> intro h <;> rw [h] <;> ext <;> simp <;> ring
  · have hu1 : u = 1 := by linarith [hu.2, hw.1]
    have hw0 : w = 0 := by linarith [hu.2, hw.1]
    subst hu1; subst hw0
    rw [nashA_bdry]; norm_num

lemma nashB_iff (u w : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) (p : ℝ × ℝ) :
    IsTurfNashB (1/2) u w p ↔ p = ((1 + u - w) / 3, (2 + w - u) / 3) := by
  by_cases hb : -1 < u - w
  · have := (lemma_2_region_1 (1/2) 0 0 u w ⟨le_refl _, by norm_num⟩
      ⟨le_refl _, by norm_num⟩ hu hw ⟨by norm_num, by linarith⟩).2 p
    rw [this]
    constructor <;> intro h <;> rw [h] <;> ext <;> simp <;> ring
  · have hu1 : u = 0 := by linarith [hu.1, hw.2]
    have hw0 : w = 1 := by linarith [hu.1, hw.2]
    subst hu1; subst hw0
    rw [nashB_bdry]; norm_num

lemma revA_A (u w : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) (p : ℝ × ℝ)
    (hp : IsTurfNashA (1/2) u w p) :
    revAturfA (1/2) u w p = (2 + u - w) ^ 2 / 18 ∧ revBturfA (1/2) u w p = (1 + w - u) ^ 2 / 18 := by
  rw [(nashA_iff u w hu hw p).1 hp]
  simp only [revAturfA, revBturfA, xaTurf]
  have e : (1 + (1 + w - u) / 3 - (2 + u - w) / 3 + u - w) / 2 = (2 + u - w) / 6 := by ring
  rw [e, max_eq_right (by linarith [hu.1, hw.2, hu.2, hw.1]),
    min_eq_right (by linarith [hu.1, hw.2, hu.2, hw.1])]
  constructor <;> ring

lemma revB_B (u w : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) (p : ℝ × ℝ)
    (hp : IsTurfNashB (1/2) u w p) :
    revAturfB (1/2) u w p = (1 + u - w) ^ 2 / 18 ∧ revBturfB (1/2) u w p = (2 + w - u) ^ 2 / 18 := by
  rw [(nashB_iff u w hu hw p).1 hp]
  simp only [revAturfB, revBturfB, xbTurf]
  have e : (1 + (2 + w - u) / 3 - (1 + u - w) / 3 + u - w) / 2 = (4 + u - w) / 6 := by ring
  rw [e, max_eq_right (by linarith [hu.1, hw.2, hu.2, hw.1]),
    min_eq_right (by linarith [hu.1, hw.2, hu.2, hw.1])]
  constructor <;> ring

end BBDSolNash



namespace BBDSolThr

lemma thr_nec (lam μ κ h : ℝ) (hl : 0 < lam) (hμ : 0 < μ) (hκ : 0 < κ)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hbig : κ < lam * (1/2) * (μ + 3/2))
    (D : ℝ → ℝ) (N : ℝ) (hDN : ∀ q ∈ Set.Icc (0:ℝ) 1, D q - N = lam * (q - h/2) * (μ + q + h/2) - κ)
    (hT : IsThresholdBR h D N) : lam * (h/2) * (μ + 3 * h / 2) = κ := by
  set g : ℝ → ℝ := fun q => lam * (q - h/2) * (μ + q + h/2) - κ with hg
  have hc : Continuous g := by fun_prop
  have gh : g h = lam * (h/2) * (μ + 3 * h / 2) - κ := by simp only [hg]; ring
  -- claim1: h < 1 → 0 ≤ g h
  have c1 : h < 1 → 0 ≤ g h := by
    intro hlt
    by_contra hneg
    have hneg : g h < 0 := not_le.mp hneg
    have ev1 : ∀ᶠ q in nhdsWithin h (Set.Ioi h), g q < 0 :=
      nhdsWithin_le_nhds ((hc.tendsto h).eventually (gt_mem_nhds hneg))
    have ev2 : ∀ᶠ q in nhdsWithin h (Set.Ioi h), q ∈ Set.Ioo h 1 := Ioo_mem_nhdsGT hlt
    obtain ⟨q, hq1, hq2⟩ := (ev1.and ev2).exists
    have := (hT q ⟨by linarith [hq2.1], hq2.2.le⟩).1 hq2.1
    have e := hDN q ⟨by linarith [hq2.1], hq2.2.le⟩
    simp only [hg] at hq1
    linarith
  have c2 : 0 < h → g h ≤ 0 := by
    intro hpos
    by_contra hneg
    have hneg : 0 < g h := not_le.mp hneg
    have ev1 : ∀ᶠ q in nhdsWithin h (Set.Iio h), 0 < g q :=
      nhdsWithin_le_nhds ((hc.tendsto h).eventually (lt_mem_nhds hneg))
    have ev2 : ∀ᶠ q in nhdsWithin h (Set.Iio h), q ∈ Set.Ioo 0 h := Ioo_mem_nhdsLT hpos
    obtain ⟨q, hq1, hq2⟩ := (ev1.and ev2).exists
    have := (hT q ⟨hq2.1.le, by linarith [hq2.2]⟩).2 hq2.2
    have e := hDN q ⟨hq2.1.le, by linarith [hq2.2]⟩
    simp only [hg] at hq1
    linarith
  have hpos : 0 < h := by
    rcases lt_or_eq_of_le h0 with h' | h'
    · exact h'
    · exfalso
      have := c1 (by linarith)
      rw [gh, ← h'] at this; linarith
  have hlt : h < 1 := by
    rcases lt_or_eq_of_le h1 with h' | h'
    · exact h'
    · exfalso
      have := c2 hpos
      rw [gh, h'] at this; nlinarith
  have := c1 hlt
  have := c2 hpos
  linarith

lemma thr_suff (lam μ κ h : ℝ) (hl : 0 < lam) (hμ : 0 < μ)
    (h0 : 0 ≤ h) (heq : lam * (h/2) * (μ + 3 * h / 2) = κ)
    (D : ℝ → ℝ) (N : ℝ) (hDN : ∀ q ∈ Set.Icc (0:ℝ) 1, D q - N = lam * (q - h/2) * (μ + q + h/2) - κ) :
    IsThresholdBR h D N := by
  intro q hq
  have e := hDN q hq
  have key : D q - N = lam * (q - h) * (μ + q + h) := by rw [e, ← heq]; ring
  have hpos : 0 < μ + q + h := by linarith [hq.1]
  constructor
  · intro hlt
    have : 0 ≤ lam * (q - h) * (μ + q + h) := by
      apply mul_nonneg (mul_nonneg hl.le (by linarith)) hpos.le
    linarith
  · intro hlt
    have : lam * (q - h) * (μ + q + h) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)) hpos.le
    linarith

end BBDSolThr


namespace BBDSolIneq

lemma amgm_up (P y r : ℝ) (hP2 : P ^ 2 = y) : 2 * r * P ≤ y + r ^ 2 := by
  nlinarith [sq_nonneg (P - r)]

lemma amgm_low (Q y r : ℝ) (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = y) : 2 * r * y ≤ Q * (y + r ^ 2) := by
  have h1 : 0 ≤ Q * (Q - r) ^ 2 := mul_nonneg hQ (sq_nonneg _)
  have h2 : Q * (Q - r) ^ 2 = Q * (y + r ^ 2) - 2 * r * y := by rw [← hQ2]; ring
  linarith

lemma pieceI_gen (α β γ P Q yP yQ r1 r2 : ℝ) (ha : α ≤ 0) (hb : 0 ≤ β) (r1p : 0 < r1)
    (hyQ : 0 ≤ yQ) (hP2 : P ^ 2 = yP) (hQ : 0 ≤ Q) (hQ2 : Q ^ 2 = yQ)
    (hpos : 0 < (yQ + r2 ^ 2) * α * (yP + r1 ^ 2) + 2 * r1 * β * (2 * r2 * yQ)
        + 2 * r1 * (yQ + r2 ^ 2) * γ) : 0 < α * P + β * Q + γ := by
  have F1 := amgm_up P yP r1 hP2
  have F2 := amgm_low Q yQ r2 hQ hQ2
  have yQp : 0 ≤ yQ + r2 ^ 2 := by positivity
  have G1 := mul_le_mul_of_nonpos_left F1 (mul_nonpos_of_nonpos_of_nonneg ha yQp)
  have G2 := mul_le_mul_of_nonneg_left F2 (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * r1) hb)
  have M : (yQ + r2 ^ 2) * α * (yP + r1 ^ 2) + 2 * r1 * β * (2 * r2 * yQ)
      + 2 * r1 * (yQ + r2 ^ 2) * γ ≤ (2 * r1 * (yQ + r2 ^ 2)) * (α * P + β * Q + γ) := by
    linear_combination G1 + G2
  have Mp : 0 ≤ 2 * r1 * (yQ + r2 ^ 2) := by positivity
  exact pos_of_mul_pos_right (lt_of_lt_of_le hpos M) Mp

lemma pieceII_gen (α β γ P Q yP yQ r1 r2 : ℝ) (ha : α ≤ 0) (hb : β ≤ 0) (r1p : 0 < r1)
    (r2p : 0 < r2) (hP2 : P ^ 2 = yP) (hQ2 : Q ^ 2 = yQ)
    (hpos : 0 < 2 * r2 * α * (yP + r1 ^ 2) + 2 * r1 * β * (yQ + r2 ^ 2) + 4 * r1 * r2 * γ) :
    0 < α * P + β * Q + γ := by
  have F1 := amgm_up P yP r1 hP2
  have F2 := amgm_up Q yQ r2 hQ2
  have G1 := mul_le_mul_of_nonpos_left F1 (mul_nonpos_of_nonneg_of_nonpos
    (by positivity : (0:ℝ) ≤ 2 * r2) ha)
  have G2 := mul_le_mul_of_nonpos_left F2 (mul_nonpos_of_nonneg_of_nonpos
    (by positivity : (0:ℝ) ≤ 2 * r1) hb)
  have M : 2 * r2 * α * (yP + r1 ^ 2) + 2 * r1 * β * (yQ + r2 ^ 2) + 4 * r1 * r2 * γ
      ≤ (4 * r1 * r2) * (α * P + β * Q + γ) := by linear_combination G1 + G2
  have Mp : 0 ≤ 4 * r1 * r2 := by positivity
  exact pos_of_mul_pos_right (lt_of_lt_of_le hpos M) Mp

lemma pieceIII_gen (α β γ P Q yP yQ r1 r2 : ℝ) (ha : 0 ≤ α) (hb : β ≤ 0)
    (r2p : 0 < r2) (hyP : 0 ≤ yP) (hP : 0 ≤ P) (hP2 : P ^ 2 = yP) (hQ2 : Q ^ 2 = yQ)
    (hpos : 0 < 2 * r2 * α * (2 * r1 * yP) + (yP + r1 ^ 2) * β * (yQ + r2 ^ 2)
          + (yP + r1 ^ 2) * 2 * r2 * γ) :
    0 < α * P + β * Q + γ := by
  have F1 := amgm_low P yP r1 hP hP2
  have F2 := amgm_up Q yQ r2 hQ2
  have yPp : 0 ≤ yP + r1 ^ 2 := by positivity
  have G1 := mul_le_mul_of_nonneg_left F1 (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * r2) ha)
  have G2 := mul_le_mul_of_nonpos_left F2 (mul_nonpos_of_nonneg_of_nonpos yPp hb)
  have M : 2 * r2 * α * (2 * r1 * yP) + (yP + r1 ^ 2) * β * (yQ + r2 ^ 2)
      + (yP + r1 ^ 2) * 2 * r2 * γ ≤ ((yP + r1 ^ 2) * 2 * r2) * (α * P + β * Q + γ) := by
    linear_combination G1 + G2
  have Mp : 0 ≤ (yP + r1 ^ 2) * 2 * r2 := by positivity
  exact pos_of_mul_pos_right (lt_of_lt_of_le hpos M) Mp

lemma polyI (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2) :
    0 < x ^ 2 * (126*x^8 + 3192*x^7 + 4570*x^6 + 29608*x^5
            - 84595*x^4 - 8158*x^3 + 357120*x^2 + 1130112*x + 6718464) / 1259712 := by
  have h3 : x ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hx0.le hx2 3
  have h4 : x ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hx0.le hx2 4
  have : 0 ≤ 126*x^8 + 3192*x^7 + 4570*x^6 + 29608*x^5 + 357120*x^2 + 1130112*x := by
    positivity
  have : 0 < 126*x^8 + 3192*x^7 + 4570*x^6 + 29608*x^5
            - 84595*x^4 - 8158*x^3 + 357120*x^2 + 1130112*x + 6718464 := by
    norm_num at h3 h4; linarith
  positivity

lemma polyII (t : ℝ) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    0 < (21280 * t^7 + 432348/5 * t^6 + 7413711/125 * t^5 + 199956203/625 * t^4
             - 36798461418/15625 * t^3 + 14358084217224/1953125 * t^2
             + 1067294297185952/48828125 * t + 19557843880147584/1220703125) / 3936600 := by
  have h32 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one t0 t1 (by norm_num : 2 ≤ 3)
  have : 0 ≤ 21280 * t^7 + 432348/5 * t^6 + 7413711/125 * t^5 + 199956203/625 * t^4
       + 1067294297185952/48828125 * t := by positivity
  have : 0 ≤ t ^ 2 := sq_nonneg t
  have : 0 < 21280 * t^7 + 432348/5 * t^6 + 7413711/125 * t^5 + 199956203/625 * t^4
             - 36798461418/15625 * t^3 + 14358084217224/1953125 * t^2
             + 1067294297185952/48828125 * t + 19557843880147584/1220703125 := by linarith
  positivity

lemma polyIII (t : ℝ) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    0 < (-11788 * t^6 - 194334/5 * t^5 - 8135269/20 * t^4 - 312069121/100 * t^3
              + 39623253039/8000 * t^2 + 16583085390713/400000 * t
              + 788776552749777/16000000) / 1080000 := by
  have h3 : t ^ 3 ≤ 1 := pow_le_one₀ t0 t1
  have h4 : t ^ 4 ≤ 1 := pow_le_one₀ t0 t1
  have h5 : t ^ 5 ≤ 1 := pow_le_one₀ t0 t1
  have h6 : t ^ 6 ≤ 1 := pow_le_one₀ t0 t1
  have : 0 ≤ 39623253039/8000 * t^2 + 16583085390713/400000 * t := by positivity
  have : 0 < (-11788 * t^6 - 194334/5 * t^5 - 8135269/20 * t^4 - 312069121/100 * t^3
              + 39623253039/8000 * t^2 + 16583085390713/400000 * t
              + 788776552749777/16000000) := by linarith
  positivity

lemma key_ineq (x P Q : ℝ) (hx0 : 0 < x) (hx3 : x < 3) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hP2 : P ^ 2 = (1 + x) ^ 2 + 8) (hQ2 : Q ^ 2 = (1 + x) ^ 2 + 3) :
    0 < ((42 * (((1 + x) ^ 2 - 1) / 108) - 4) / 3) * P
      + ((64 / 27 - 56 * (((1 + x) ^ 2 - 1) / 108)) / 2) * Q
      + ((14 * (((1 + x) ^ 2 - 1) / 108) - 4 / 27) * (1 + x) + 16 / 9) := by
  have hc0 : 0 ≤ ((1 + x) ^ 2 - 1) / 108 := by nlinarith
  rcases le_total 0 ((64 / 27 - 56 * (((1 + x) ^ 2 - 1) / 108)) / 2) with hb | hb
  · have ha : (42 * (((1 + x) ^ 2 - 1) / 108) - 4) / 3 ≤ 0 := by linarith
    have hx2 : x ≤ 2 := by
      by_contra h; push Not at h
      have : 2 * 2 < x * x := mul_lt_mul'' h h (by norm_num) (by norm_num)
      nlinarith
    apply pieceI_gen _ _ _ P Q _ _ (3 + x / 3 + 4 / 27 * x ^ 2) (2 + x / 2 + 3 / 16 * x ^ 2)
      ha hb (by positivity) (by positivity) hP2 hQ hQ2
    have e : ((1 + x) ^ 2 + 3 + (2 + x / 2 + 3 / 16 * x ^ 2) ^ 2) *
        ((42 * (((1 + x) ^ 2 - 1) / 108) - 4) / 3) * ((1 + x) ^ 2 + 8 + (3 + x / 3 + 4 / 27 * x ^ 2) ^ 2)
        + 2 * (3 + x / 3 + 4 / 27 * x ^ 2) * ((64 / 27 - 56 * (((1 + x) ^ 2 - 1) / 108)) / 2)
          * (2 * (2 + x / 2 + 3 / 16 * x ^ 2) * ((1 + x) ^ 2 + 3))
        + 2 * (3 + x / 3 + 4 / 27 * x ^ 2) * ((1 + x) ^ 2 + 3 + (2 + x / 2 + 3 / 16 * x ^ 2) ^ 2)
          * ((14 * (((1 + x) ^ 2 - 1) / 108) - 4 / 27) * (1 + x) + 16 / 9)
        = x ^ 2 * (126*x^8 + 3192*x^7 + 4570*x^6 + 29608*x^5
            - 84595*x^4 - 8158*x^3 + 357120*x^2 + 1130112*x + 6718464) / 1259712 := by ring
    rw [e]; exact polyI x hx0 hx2
  · rcases le_total ((42 * (((1 + x) ^ 2 - 1) / 108) - 4) / 3) 0 with ha | ha
    · have hxl : 136 / 100 ≤ x := by
        by_contra h; push Not at h
        have : x * x < 136 / 100 * (136 / 100) := mul_lt_mul'' h h hx0.le hx0.le
        nlinarith
      have hxu : x ≤ 236 / 100 := by
        by_contra h; push Not at h
        have : 236 / 100 * (236 / 100) < x * x := mul_lt_mul'' h h (by norm_num) (by norm_num)
        nlinarith
      apply pieceII_gen _ _ _ P Q _ _ (3 + x / 3 + 4 / 27 * x ^ 2) (3 / 2 + 19 / 20 * x)
        ha hb (by positivity) (by positivity) hP2 hQ2
      obtain ⟨t, rfl⟩ : ∃ t, x = 136 / 100 + t := ⟨x - 136 / 100, by ring⟩
      have e : 2 * (3 / 2 + 19 / 20 * (136 / 100 + t)) * ((42 * (((1 + (136 / 100 + t)) ^ 2 - 1) / 108) - 4) / 3)
          * ((1 + (136 / 100 + t)) ^ 2 + 8 + (3 + (136 / 100 + t) / 3 + 4 / 27 * (136 / 100 + t) ^ 2) ^ 2)
        + 2 * (3 + (136 / 100 + t) / 3 + 4 / 27 * (136 / 100 + t) ^ 2)
          * ((64 / 27 - 56 * (((1 + (136 / 100 + t)) ^ 2 - 1) / 108)) / 2)
          * ((1 + (136 / 100 + t)) ^ 2 + 3 + (3 / 2 + 19 / 20 * (136 / 100 + t)) ^ 2)
        + 4 * (3 + (136 / 100 + t) / 3 + 4 / 27 * (136 / 100 + t) ^ 2) * (3 / 2 + 19 / 20 * (136 / 100 + t))
          * ((14 * (((1 + (136 / 100 + t)) ^ 2 - 1) / 108) - 4 / 27) * (1 + (136 / 100 + t)) + 16 / 9)
        = (21280 * t^7 + 432348/5 * t^6 + 7413711/125 * t^5 + 199956203/625 * t^4
             - 36798461418/15625 * t^3 + 14358084217224/1953125 * t^2
             + 1067294297185952/48828125 * t + 19557843880147584/1220703125) / 3936600 := by ring
      rw [e]; exact polyII t (by linarith) (by linarith)
    · have hxl : 235 / 100 ≤ x := by
        by_contra h; push Not at h
        have : x * x < 235 / 100 * (235 / 100) := mul_lt_mul'' h h hx0.le hx0.le
        nlinarith
      apply pieceIII_gen _ _ _ P Q _ _ (5 / 2 + 4 / 5 * x) (3 / 2 + 19 / 20 * x)
        ha hb (by positivity) (by positivity) hP hP2 hQ2
      obtain ⟨t, rfl⟩ : ∃ t, x = 235 / 100 + t := ⟨x - 235 / 100, by ring⟩
      have e : 2 * (3 / 2 + 19 / 20 * (235 / 100 + t)) * ((42 * (((1 + (235 / 100 + t)) ^ 2 - 1) / 108) - 4) / 3)
          * (2 * (5 / 2 + 4 / 5 * (235 / 100 + t)) * ((1 + (235 / 100 + t)) ^ 2 + 8))
        + ((1 + (235 / 100 + t)) ^ 2 + 8 + (5 / 2 + 4 / 5 * (235 / 100 + t)) ^ 2)
          * ((64 / 27 - 56 * (((1 + (235 / 100 + t)) ^ 2 - 1) / 108)) / 2)
          * ((1 + (235 / 100 + t)) ^ 2 + 3 + (3 / 2 + 19 / 20 * (235 / 100 + t)) ^ 2)
        + ((1 + (235 / 100 + t)) ^ 2 + 8 + (5 / 2 + 4 / 5 * (235 / 100 + t)) ^ 2) * 2
          * (3 / 2 + 19 / 20 * (235 / 100 + t))
          * ((14 * (((1 + (235 / 100 + t)) ^ 2 - 1) / 108) - 4 / 27) * (1 + (235 / 100 + t)) + 16 / 9)
        = (-11788 * t^6 - 194334/5 * t^5 - 8135269/20 * t^4 - 312069121/100 * t^3
              + 39623253039/8000 * t^2 + 16583085390713/400000 * t
              + 788776552749777/16000000) / 1080000 := by ring
      rw [e]; exact polyIII t (by linarith) (by linarith)

end BBDSolIneq



namespace BBDSolMain
open BBDSolInt BBDSolNash BBDSolThr BBDSolIneq

lemma bel_mem {h q : ℝ} (hh : h ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    bel h q ∈ Set.Icc (0:ℝ) 1 := by
  unfold bel; split_ifs <;> constructor <;> linarith [hh.1, hh.2, hq.1, hq.2]

lemma int2 (h1 h2 : ℝ) (hh1 : h1 ∈ Set.Icc (0:ℝ) 1) (hh2 : h2 ∈ Set.Icc (0:ℝ) 1)
    (α β1 γ1 δ1 β2 γ2 δ2 : ℝ) (f : ℝ → ℝ)
    (hf : ∀ q ∈ Set.Icc (0:ℝ) 1, f q = α + β1 * bel h1 q + γ1 * bel h1 q ^ 2 + δ1 * ind h1 q
        + β2 * bel h2 q + γ2 * bel h2 q ^ 2 + δ2 * ind h2 q) :
    ∫ q in (0:ℝ)..1, f q = α + β1 / 2 + γ1 * (1 / 3 - h1 ^ 3 / 12) + δ1 * (1 - h1)
        + β2 / 2 + γ2 * (1 / 3 - h2 ^ 3 / 12) + δ2 * (1 - h2) := by
  rw [intervalIntegral.integral_congr (g := fun q => α + β1 * bel h1 q + γ1 * bel h1 q ^ 2
      + δ1 * ind h1 q + β2 * bel h2 q + γ2 * bel h2 q ^ 2 + δ2 * ind h2 q)]
  · exact moment h1 h2 hh1.1 hh1.2 hh2.1 hh2.2 α β1 γ1 δ1 β2 γ2 δ2
  · intro q hq
    rw [Set.uIcc_of_le zero_le_one] at hq
    exact hf q hq

def NashA (σA : ℝ → ℝ → ℝ × ℝ) : Prop :=
  ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashA (1/2) u w (σA u w)
def NashB (σB : ℝ → ℝ → ℝ × ℝ) : Prop :=
  ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashB (1/2) u w (σB u w)

noncomputable def m (h : ℝ) : ℝ := 1 / 3 - h ^ 3 / 12

lemma TI1 (σA : ℝ → ℝ → ℝ × ℝ) (hA : NashA σA) (h u : ℝ) (hh : h ∈ Set.Icc (0:ℝ) 1)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    ∫ qb in (0:ℝ)..1, revAturfA (1/2) u (bel h qb) (σA u (bel h qb))
      = ((2 + u) ^ 2 - (2 + u) + m h) / 18 := by
  refine (int2 h h hh hh ((2 + u) ^ 2 / 18) (-(2 + u) / 9) (1/18) 0 0 0 0 _ ?_).trans
    (by unfold m; ring)
  intro q hq
  rw [(revA_A u (bel h q) hu (bel_mem hh hq) _ (hA u hu _ (bel_mem hh hq))).1]; ring

lemma TI2 (σB : ℝ → ℝ → ℝ × ℝ) (hB : NashB σB) (h u : ℝ) (hh : h ∈ Set.Icc (0:ℝ) 1)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    ∫ qb in (0:ℝ)..1, revAturfB (1/2) u (bel h qb) (σB u (bel h qb))
      = ((1 + u) ^ 2 - (1 + u) + m h) / 18 := by
  refine (int2 h h hh hh ((1 + u) ^ 2 / 18) (-(1 + u) / 9) (1/18) 0 0 0 0 _ ?_).trans
    (by unfold m; ring)
  intro q hq
  rw [(revB_B u (bel h q) hu (bel_mem hh hq) _ (hB u hu _ (bel_mem hh hq))).1]; ring

lemma TI3 (σB : ℝ → ℝ → ℝ × ℝ) (hB : NashB σB) (h w : ℝ) (hh : h ∈ Set.Icc (0:ℝ) 1)
    (hw : w ∈ Set.Icc (0:ℝ) 1) :
    ∫ qa in (0:ℝ)..1, revBturfB (1/2) (bel h qa) w (σB (bel h qa) w)
      = ((2 + w) ^ 2 - (2 + w) + m h) / 18 := by
  refine (int2 h h hh hh ((2 + w) ^ 2 / 18) (-(2 + w) / 9) (1/18) 0 0 0 0 _ ?_).trans
    (by unfold m; ring)
  intro q hq
  rw [(revB_B (bel h q) w (bel_mem hh hq) hw _ (hB _ (bel_mem hh hq) w hw)).2]; ring

lemma TI4 (σA : ℝ → ℝ → ℝ × ℝ) (hA : NashA σA) (h w : ℝ) (hh : h ∈ Set.Icc (0:ℝ) 1)
    (hw : w ∈ Set.Icc (0:ℝ) 1) :
    ∫ qa in (0:ℝ)..1, revBturfA (1/2) (bel h qa) w (σA (bel h qa) w)
      = ((1 + w) ^ 2 - (1 + w) + m h) / 18 := by
  refine (int2 h h hh hh ((1 + w) ^ 2 / 18) (-(1 + w) / 9) (1/18) 0 0 0 0 _ ?_).trans
    (by unfold m; ring)
  intro q hq
  rw [(revA_A (bel h q) w (bel_mem hh hq) hw _ (hA _ (bel_mem hh hq) w hw)).2]; ring

lemma TIUA (σA σB : ℝ → ℝ → ℝ × ℝ) (hA : NashA σA) (hB : NashB σB) (h u : ℝ)
    (hh : h ∈ Set.Icc (0:ℝ) 1) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    ∫ qb in (0:ℝ)..1, (revAturfA (1/2) u (bel h qb) (σA u (bel h qb))
        + revAturfB (1/2) u (bel h qb) (σB u (bel h qb)))
      = ((2 + u) ^ 2 - (2 + u) + (1 + u) ^ 2 - (1 + u) + 2 * m h) / 18 := by
  refine (int2 h h hh hh (((2 + u) ^ 2 + (1 + u) ^ 2) / 18) (-(3 + 2 * u) / 9) (2/18)
    0 0 0 0 _ ?_).trans (by unfold m; ring)
  intro q hq
  rw [(revA_A u (bel h q) hu (bel_mem hh hq) _ (hA u hu _ (bel_mem hh hq))).1,
    (revB_B u (bel h q) hu (bel_mem hh hq) _ (hB u hu _ (bel_mem hh hq))).1]; ring

lemma TIUB (σA σB : ℝ → ℝ → ℝ × ℝ) (hA : NashA σA) (hB : NashB σB) (h w : ℝ)
    (hh : h ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) :
    ∫ qa in (0:ℝ)..1, (revBturfA (1/2) (bel h qa) w (σA (bel h qa) w)
        + revBturfB (1/2) (bel h qa) w (σB (bel h qa) w))
      = ((1 + w) ^ 2 - (1 + w) + (2 + w) ^ 2 - (2 + w) + 2 * m h) / 18 := by
  refine (int2 h h hh hh (((1 + w) ^ 2 + (2 + w) ^ 2) / 18) (-(3 + 2 * w) / 9) (2/18)
    0 0 0 0 _ ?_).trans (by unfold m; ring)
  intro q hq
  rw [(revA_A (bel h q) w (bel_mem hh hq) hw _ (hA _ (bel_mem hh hq) w hw)).2,
    (revB_B (bel h q) w (bel_mem hh hq) hw _ (hB _ (bel_mem hh hq) w hw)).2]; ring

lemma half_mem {h : ℝ} (hh : h ∈ Set.Icc (0:ℝ) 1) : h / 2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-- equation of own threshold -/
def EqOwn (c h : ℝ) : Prop := 1 / 18 * (h / 2) * (3 + 3 * h / 2) = c / 2
def EqNew (c h : ℝ) : Prop := 1 / 18 * (h / 2) * (1 + 3 * h / 2) = c / 2
def EqUni (c h : ℝ) : Prop := 1 / 9 * (h / 2) * (2 + 3 * h / 2) = c

lemma bbd_nec (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileBBD)
    (he : IsStage2EqBBD c (1 / 2) e) :
    EqOwn c e.qao ∧ EqNew c e.qan ∧ EqOwn c e.qbo ∧ EqNew c e.qbn := by
  obtain ⟨hao, han, hbo, hbn, hA, hB, tao, tan, tbo, tbn⟩ := he
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine thr_nec (1/18) 3 (c/2) e.qao (by norm_num) (by norm_num) (by linarith) hao.1 hao.2
      (by linarith) _ _ ?_ tao
    intro q hq
    try simp only []
    rw [TI1 e.σA hA e.qbn q hbn hq, TI1 e.σA hA e.qbn _ hbn (half_mem hao)]; ring
  · refine thr_nec (1/18) 1 (c/2) e.qan (by norm_num) (by norm_num) (by linarith) han.1 han.2
      (by linarith) _ _ ?_ tan
    intro q hq
    try simp only []
    rw [TI2 e.σB hB e.qbo q hbo hq, TI2 e.σB hB e.qbo _ hbo (half_mem han)]; ring
  · refine thr_nec (1/18) 3 (c/2) e.qbo (by norm_num) (by norm_num) (by linarith) hbo.1 hbo.2
      (by linarith) _ _ ?_ tbo
    intro q hq
    try simp only []
    rw [TI3 e.σB hB e.qan q han hq, TI3 e.σB hB e.qan _ han (half_mem hbo)]; ring
  · refine thr_nec (1/18) 1 (c/2) e.qbn (by norm_num) (by norm_num) (by linarith) hbn.1 hbn.2
      (by linarith) _ _ ?_ tbn
    intro q hq
    try simp only []
    rw [TI4 e.σA hA e.qao q hao hq, TI4 e.σA hA e.qao _ hao (half_mem hbn)]; ring

lemma bbd_suff (c : ℝ) (e : ProfileBBD)
    (hao : e.qao ∈ Set.Icc (0:ℝ) 1) (han : e.qan ∈ Set.Icc (0:ℝ) 1)
    (hbo : e.qbo ∈ Set.Icc (0:ℝ) 1) (hbn : e.qbn ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA e.σA) (hB : NashB e.σB)
    (h1 : EqOwn c e.qao) (h2 : EqNew c e.qan) (h3 : EqOwn c e.qbo) (h4 : EqNew c e.qbn) :
    IsStage2EqBBD c (1 / 2) e := by
  refine ⟨hao, han, hbo, hbn, hA, hB, ?_, ?_, ?_, ?_⟩
  · refine thr_suff (1/18) 3 (c/2) e.qao (by norm_num) (by norm_num) hao.1 h1 _ _ ?_
    intro q hq
    try simp only []
    rw [TI1 e.σA hA e.qbn q hbn hq, TI1 e.σA hA e.qbn _ hbn (half_mem hao)]; ring
  · refine thr_suff (1/18) 1 (c/2) e.qan (by norm_num) (by norm_num) han.1 h2 _ _ ?_
    intro q hq
    try simp only []
    rw [TI2 e.σB hB e.qbo q hbo hq, TI2 e.σB hB e.qbo _ hbo (half_mem han)]; ring
  · refine thr_suff (1/18) 3 (c/2) e.qbo (by norm_num) (by norm_num) hbo.1 h3 _ _ ?_
    intro q hq
    try simp only []
    rw [TI3 e.σB hB e.qan q han hq, TI3 e.σB hB e.qan _ han (half_mem hbo)]; ring
  · refine thr_suff (1/18) 1 (c/2) e.qbn (by norm_num) (by norm_num) hbn.1 h4 _ _ ?_
    intro q hq
    try simp only []
    rw [TI4 e.σA hA e.qao q hao hq, TI4 e.σA hA e.qao _ hao (half_mem hbn)]; ring

lemma u_nec (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (u : ProfileU)
    (hu : IsStage2EqU c (1 / 2) u) : EqUni c u.qa ∧ EqUni c u.qb := by
  obtain ⟨ha, hb, hA, hB, ta, tb⟩ := hu
  refine ⟨?_, ?_⟩
  · refine thr_nec (1/9) 2 c u.qa (by norm_num) (by norm_num) hc0 ha.1 ha.2
      (by linarith) _ _ ?_ ta
    intro q hq
    try simp only []
    rw [TIUA u.σA u.σB hA hB u.qb q hb hq, TIUA u.σA u.σB hA hB u.qb _ hb (half_mem ha)]; ring
  · refine thr_nec (1/9) 2 c u.qb (by norm_num) (by norm_num) hc0 hb.1 hb.2
      (by linarith) _ _ ?_ tb
    intro q hq
    try simp only []
    rw [TIUB u.σA u.σB hA hB u.qa q ha hq, TIUB u.σA u.σB hA hB u.qa _ ha (half_mem hb)]; ring

lemma u_suff (c : ℝ) (u : ProfileU)
    (ha : u.qa ∈ Set.Icc (0:ℝ) 1) (hb : u.qb ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA u.σA) (hB : NashB u.σB) (h1 : EqUni c u.qa) (h2 : EqUni c u.qb) :
    IsStage2EqU c (1 / 2) u := by
  refine ⟨ha, hb, hA, hB, ?_, ?_⟩
  · refine thr_suff (1/9) 2 c u.qa (by norm_num) (by norm_num) ha.1 h1 _ _ ?_
    intro q hq
    try simp only []
    rw [TIUA u.σA u.σB hA hB u.qb q hb hq, TIUA u.σA u.σB hA hB u.qb _ hb (half_mem ha)]; ring
  · refine thr_suff (1/9) 2 c u.qb (by norm_num) (by norm_num) hb.1 h2 _ _ ?_
    intro q hq
    try simp only []
    rw [TIUB u.σA u.σB hA hB u.qa q ha hq, TIUB u.σA u.σB hA hB u.qa _ ha (half_mem hb)]; ring

end BBDSolMain



namespace BBDSolFinal
open BBDSolInt BBDSolNash BBDSolThr BBDSolIneq BBDSolMain

lemma exA_BBD (c : ℝ) (e : ProfileBBD)
    (hao : e.qao ∈ Set.Icc (0:ℝ) 1) (han : e.qan ∈ Set.Icc (0:ℝ) 1)
    (hbo : e.qbo ∈ Set.Icc (0:ℝ) 1) (hbn : e.qbn ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA e.σA) (hB : NashB e.σB) :
    exAnteA_BBD c (1/2) e = 8/27 - (e.qao^3 + e.qan^3 + e.qbo^3 + e.qbn^3)/216
      - c * (1 - e.qao/2 - e.qan/2) := by
  unfold exAnteA_BBD
  refine (int2 e.qao e.qan hao han ((2 + m e.qbn + m e.qbo)/18) (3/18) (1/18) (-(c/2))
    (1/18) (1/18) (-(c/2)) _ ?_).trans (by unfold m; ring)
  intro qa hqa
  have hU := bel_mem hao hqa
  have hU' := bel_mem han hqa
  refine (int2 e.qbn e.qbo hbn hbo ((2 + bel e.qao qa)^2/18 + (1 + bel e.qan qa)^2/18
      - (if e.qao < qa then 1/2*c else 0) - (if e.qan < qa then (1 - 1/2)*c else 0))
    (-(2 + bel e.qao qa)/9) (1/18) 0 (-(1 + bel e.qan qa)/9) (1/18) 0 _ ?_).trans ?_
  · intro qb hqb
    beta_reduce
    rw [(revA_A _ _ hU (bel_mem hbn hqb) _ (hA _ hU _ (bel_mem hbn hqb))).1,
      (revB_B _ _ hU' (bel_mem hbo hqb) _ (hB _ hU' _ (bel_mem hbo hqb))).1]
    ring
  · unfold m ind; split_ifs <;> ring

lemma exB_BBD (c : ℝ) (e : ProfileBBD)
    (hao : e.qao ∈ Set.Icc (0:ℝ) 1) (han : e.qan ∈ Set.Icc (0:ℝ) 1)
    (hbo : e.qbo ∈ Set.Icc (0:ℝ) 1) (hbn : e.qbn ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA e.σA) (hB : NashB e.σB) :
    exAnteB_BBD c (1/2) e = 8/27 - (e.qao^3 + e.qan^3 + e.qbo^3 + e.qbn^3)/216
      - c * (1 - e.qbn/2 - e.qbo/2) := by
  unfold exAnteB_BBD
  refine (int2 e.qao e.qan hao han ((8 + m e.qbn + m e.qbo)/18 - c/2*(1 - e.qbn)
    - c/2*(1 - e.qbo)) (-3/18) (1/18) 0 (-5/18) (1/18) 0 _ ?_).trans (by unfold m; ring)
  intro qa hqa
  have hU := bel_mem hao hqa
  have hU' := bel_mem han hqa
  refine (int2 e.qbn e.qbo hbn hbo ((1 - bel e.qao qa)^2/18 + (2 - bel e.qan qa)^2/18)
    ((1 - bel e.qao qa)/9) (1/18) (-(c/2)) ((2 - bel e.qan qa)/9) (1/18) (-(c/2)) _ ?_).trans ?_
  · intro qb hqb
    beta_reduce
    rw [(revA_A _ _ hU (bel_mem hbn hqb) _ (hA _ hU _ (bel_mem hbn hqb))).2,
      (revB_B _ _ hU' (bel_mem hbo hqb) _ (hB _ hU' _ (bel_mem hbo hqb))).2]
    unfold ind; split_ifs <;> ring
  · unfold m; ring

lemma exA_U (c : ℝ) (u : ProfileU)
    (ha : u.qa ∈ Set.Icc (0:ℝ) 1) (hb : u.qb ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA u.σA) (hB : NashB u.σB) :
    exAnteA_U c (1/2) u = 8/27 - (u.qa^3 + u.qb^3)/108 - c * (1 - u.qa) := by
  unfold exAnteA_U
  refine (int2 u.qa u.qa ha ha ((2 + 2 * m u.qb)/18) (4/18) (2/18) (-c) 0 0 0 _ ?_).trans
    (by unfold m; ring)
  intro qa hqa
  have hU := bel_mem ha hqa
  refine (int2 u.qb u.qb hb hb (((2 + bel u.qa qa)^2 + (1 + bel u.qa qa)^2)/18
      - (if u.qa < qa then c else 0))
    (-(3 + 2 * bel u.qa qa)/9) (2/18) 0 0 0 0 _ ?_).trans ?_
  · intro qb hqb
    beta_reduce
    rw [(revA_A _ _ hU (bel_mem hb hqb) _ (hA _ hU _ (bel_mem hb hqb))).1,
      (revB_B _ _ hU (bel_mem hb hqb) _ (hB _ hU _ (bel_mem hb hqb))).1]
    ring
  · unfold m ind; split_ifs <;> ring

lemma exB_U (c : ℝ) (u : ProfileU)
    (ha : u.qa ∈ Set.Icc (0:ℝ) 1) (hb : u.qb ∈ Set.Icc (0:ℝ) 1)
    (hA : NashA u.σA) (hB : NashB u.σB) :
    exAnteB_U c (1/2) u = 8/27 - (u.qa^3 + u.qb^3)/108 - c * (1 - u.qb) := by
  unfold exAnteB_U
  refine (int2 u.qa u.qa ha ha ((8 + 2 * m u.qb)/18 - c * (1 - u.qb)) (-8/18) (2/18) 0 0 0 0
    _ ?_).trans (by unfold m; ring)
  intro qa hqa
  have hU := bel_mem ha hqa
  refine (int2 u.qb u.qb hb hb (((1 - bel u.qa qa)^2 + (2 - bel u.qa qa)^2)/18)
    ((3 - 2 * bel u.qa qa)/9) (2/18) (-c) 0 0 0 _ ?_).trans ?_
  · intro qb hqb
    beta_reduce
    rw [(revA_A _ _ hU (bel_mem hb hqb) _ (hA _ hU _ (bel_mem hb hqb))).2,
      (revB_B _ _ hU (bel_mem hb hqb) _ (hB _ hU _ (bel_mem hb hqb))).2]
    unfold ind; split_ifs <;> ring
  · unfold m; ring

lemma profit_gap (c a b h : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (ha0 : 0 ≤ a)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hh0 : 0 ≤ h)
    (ea : a ^ 2 + 2 * a = 12 * c) (eb : 3 * b ^ 2 + 2 * b = 36 * c)
    (eh : 3 * h ^ 2 + 4 * h = 36 * c) :
    8/27 - (h^3 + h^3)/108 - c * (1 - h) < 8/27 - (a^3 + b^3 + a^3 + b^3)/216
      - c * (1 - a/2 - b/2) := by
  have hb0 : 0 < b := by
    rcases lt_or_eq_of_le hb.1 with h' | h'
    · exact h'
    · rw [← h'] at eb; linarith
  have hb1 : b < 1 := by
    rcases lt_or_eq_of_le hb.2 with h' | h'
    · exact h'
    · rw [h'] at eb; linarith
  have K := key_ineq (3 * b) (3 * (a + 1)) (3 * h + 2) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linear_combination 9 * ea - 3 * eb)
    (by linear_combination 3 * eh - 3 * eb)
  have hcx : ((1 + 3 * b) ^ 2 - 1) / 108 = c := by linear_combination 1/36 * eb
  rw [hcx] at K
  have hd : (8/27 - (a^3 + b^3 + a^3 + b^3)/216 - c * (1 - a/2 - b/2))
      - (8/27 - (h^3 + h^3)/108 - c * (1 - h)) =
      (((42 * c - 4) / 3) * (3 * (a + 1)) + ((64 / 27 - 56 * c) / 2) * (3 * h + 2)
        + ((14 * c - 4 / 27) * (1 + 3 * b) + 16 / 9)) / 108 := by
    linear_combination (2 * (h / 3 - 4 / 9) * eh - (a - 2) * ea - (b / 3 - 2 / 9) * eb) / 108
  linarith


lemma own_rel {c h : ℝ} (H : EqOwn c h) : h ^ 2 + 2 * h = 12 * c := by
  unfold EqOwn at H; linear_combination 24 * H
lemma new_rel {c h : ℝ} (H : EqNew c h) : 3 * h ^ 2 + 2 * h = 36 * c := by
  unfold EqNew at H; linear_combination 72 * H
lemma uni_rel {c h : ℝ} (H : EqUni c h) : 3 * h ^ 2 + 4 * h = 36 * c := by
  unfold EqUni at H; linear_combination 36 * H

lemma own_exists (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    ∃ a, a ∈ Set.Icc (0:ℝ) 1 ∧ EqOwn c a := by
  have hs := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + 12 * c)
  have hs0 := Real.sqrt_nonneg (1 + 12 * c)
  refine ⟨Real.sqrt (1 + 12 * c) - 1, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  unfold EqOwn; linear_combination (1/24) * hs

lemma new_exists (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    ∃ b, b ∈ Set.Icc (0:ℝ) 1 ∧ EqNew c b := by
  have hs := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + 108 * c)
  have hs0 := Real.sqrt_nonneg (1 + 108 * c)
  refine ⟨(Real.sqrt (1 + 108 * c) - 1) / 3, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  unfold EqNew; linear_combination (1/216) * hs

lemma uni_exists (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    ∃ h, h ∈ Set.Icc (0:ℝ) 1 ∧ EqUni c h := by
  have hs := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + 27 * c)
  have hs0 := Real.sqrt_nonneg (1 + 27 * c)
  refine ⟨2 * (Real.sqrt (1 + 27 * c) - 1) / 3, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  unfold EqUni; linear_combination (1/27) * hs

lemma nashA_star : NashA (fun u w => ((2 + u - w) / 3, (1 + w - u) / 3)) :=
  fun u hu w hw => (nashA_iff u w hu hw _).2 rfl
lemma nashB_star : NashB (fun u w => ((1 + u - w) / 3, (2 + w - u) / 3)) :=
  fun u hu w hw => (nashB_iff u w hu hw _).2 rfl

lemma uniq_own {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ex : x ^ 2 + 2 * x = 12 * c)
    (ey : y ^ 2 + 2 * y = 12 * c) : x = y := by
  have : (x - y) * (x + y + 2) = 0 := by linear_combination ex - ey
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith
lemma uniq_new {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ex : 3 * x ^ 2 + 2 * x = 36 * c)
    (ey : 3 * y ^ 2 + 2 * y = 36 * c) : x = y := by
  have : (x - y) * (3 * x + 3 * y + 2) = 0 := by linear_combination ex - ey
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith
lemma uniq_uni {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ex : 3 * x ^ 2 + 4 * x = 36 * c)
    (ey : 3 * y ^ 2 + 4 * y = 36 * c) : x = y := by
  have : (x - y) * (3 * x + 3 * y + 4) = 0 := by linear_combination ex - ey
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

lemma own_lt_new {c a b : ℝ} (hc0 : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ea : a ^ 2 + 2 * a = 12 * c) (eb : 3 * b ^ 2 + 2 * b = 36 * c) : a < b := by
  by_contra h
  have h : b ≤ a := not_lt.mp h
  have hb0 : 0 < b := by nlinarith
  nlinarith

theorem prop1 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∃ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e) ∧
    (∃ u : ProfileU, IsStage2EqU c (1 / 2) u) ∧
    (∀ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e → e.qao < e.qan ∧ e.qbo < e.qbn) ∧
    (∀ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e →
      ∀ qa ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
        (e.σB (bel e.qan qa) (bel e.qbo qb)).1 < (e.σA (bel e.qao qa) (bel e.qbn qb)).1 ∧
          (e.σA (bel e.qao qa) (bel e.qbn qb)).2 < (e.σB (bel e.qan qa) (bel e.qbo qb)).2) ∧
    (∀ (e : ProfileBBD) (u : ProfileU), IsStage2EqBBD c (1 / 2) e → IsStage2EqU c (1 / 2) u →
      exAnteA_U c (1 / 2) u < exAnteA_BBD c (1 / 2) e ∧
        exAnteB_U c (1 / 2) u < exAnteB_BBD c (1 / 2) e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, ea⟩ := own_exists c hc0 hc
    obtain ⟨b, hb, eb⟩ := new_exists c hc0 hc
    exact ⟨⟨a, b, a, b, _, _⟩, bbd_suff c _ ha hb ha hb nashA_star nashB_star ea eb ea eb⟩
  · obtain ⟨h, hh, eh⟩ := uni_exists c hc0 hc
    exact ⟨⟨h, h, _, _⟩, u_suff c _ hh hh nashA_star nashB_star eh eh⟩
  · intro e he
    obtain ⟨e1, e2, e3, e4⟩ := bbd_nec c hc0 hc e he
    exact ⟨own_lt_new hc0 he.1.1 he.2.1.1 (own_rel e1) (new_rel e2),
      own_lt_new hc0 he.2.2.1.1 he.2.2.2.1.1 (own_rel e3) (new_rel e4)⟩
  · intro e he qa hqa qb hqb
    obtain ⟨e1, e2, e3, e4⟩ := bbd_nec c hc0 hc e he
    obtain ⟨hao, han, hbo, hbn, hA, hB, -⟩ := he
    have hab := own_lt_new hc0 hao.1 han.1 (own_rel e1) (new_rel e2)
    have h1 := uniq_own hao.1 hbo.1 (own_rel e1) (own_rel e3)
    have h2 := uniq_new han.1 hbn.1 (new_rel e2) (new_rel e4)
    have hpA := (nashA_iff _ _ (bel_mem hao hqa) (bel_mem hbn hqb) _).1
      (hA _ (bel_mem hao hqa) _ (bel_mem hbn hqb))
    have hpB := (nashB_iff _ _ (bel_mem han hqa) (bel_mem hbo hqb) _).1
      (hB _ (bel_mem han hqa) _ (bel_mem hbo hqb))
    rw [hpA, hpB]
    simp only
    rw [← h1, ← h2]
    have hao0 : 0 < e.qao := by
      have r := own_rel e1
      rcases lt_or_eq_of_le hao.1 with h' | h'
      · exact h'
      · rw [← h'] at r; linarith
    have key : bel e.qan qa - bel e.qao qa + bel e.qan qb - bel e.qao qb < 1 := by
      unfold bel
      split_ifs <;> linarith [hqa.1, hqa.2, hqb.1, hqb.2, hao.1, han.2, hao0]
    constructor <;> linarith
  · intro e u he hu
    obtain ⟨e1, e2, e3, e4⟩ := bbd_nec c hc0 hc e he
    obtain ⟨u1, u2⟩ := u_nec c hc0 hc u hu
    obtain ⟨hao, han, hbo, hbn, hA, hB, -⟩ := he
    obtain ⟨hqa, hqb, hUA, hUB, -⟩ := hu
    have h1 := uniq_own hao.1 hbo.1 (own_rel e1) (own_rel e3)
    have h2 := uniq_new han.1 hbn.1 (new_rel e2) (new_rel e4)
    have h3 := uniq_uni hqa.1 hqb.1 (uni_rel u1) (uni_rel u2)
    rw [exA_BBD c e hao han hbo hbn hA hB, exB_BBD c e hao han hbo hbn hA hB,
      exA_U c u hqa hqb hUA hUB, exB_U c u hqa hqb hUA hUB, ← h1, ← h2, ← h3]
    have G := profit_gap c e.qao e.qan u.qa hc0 hc hao.1 han hqa.1 (own_rel e1) (new_rel e2)
      (uni_rel u1)
    constructor
    · linarith
    · linarith

end BBDSolFinal


theorem solution (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileU)
    (he : IsStage2EqU c (1 / 2) e) :
    e.qa = 2 * (Real.sqrt (1 + 27 * c) - 1) / 3 ∧
      e.qb = 2 * (Real.sqrt (1 + 27 * c) - 1) / 3 := by
  obtain ⟨u1, u2⟩ := BBDSolMain.u_nec c hc0 hc e he
  have r1 := BBDSolFinal.uni_rel u1
  have r2 := BBDSolFinal.uni_rel u2
  have ha := he.1.1
  have hb := he.2.1.1
  constructor
  · have : Real.sqrt (1 + 27 * c) = (3 * e.qa + 2) / 2 := by
      rw [show 1 + 27 * c = ((3 * e.qa + 2) / 2) ^ 2 by linear_combination (-3/4) * r1]
      exact Real.sqrt_sq (by linarith)
    rw [this]; ring
  · have : Real.sqrt (1 + 27 * c) = (3 * e.qb + 2) / 2 := by
      rw [show 1 + 27 * c = ((3 * e.qb + 2) / 2) ^ 2 by linear_combination (-3/4) * r2]
      exact Real.sqrt_sq (by linarith)
    rw [this]; ring
