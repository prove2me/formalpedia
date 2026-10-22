-- Prove2me | solution 1 for CustomReturns.WinWin.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:26:26.476211+00:00
-- url     : https://prove2.me/submissions/d14337ba-5701-4907-bde4-4dc55162cff2

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

namespace CRSol
open CustomReturns.WinWin MeasureTheory Set


theorem core (a b : ℝ) (ha : -1 ≤ a) (hb : 0 ≤ 3*a+b) :
    max 0 (min 1 b - max 0 a) * (3*a/20+9/100) +
      max 0 (1 - max 0 (max ((3*a+b)/4) b)) * ((3*a+b)/20 + 2/25) ≤ 13/125 ∧
    (max 0 (min 1 b - max 0 a) * (3*a/20+9/100) +
      max 0 (1 - max 0 (max ((3*a+b)/4) b)) * ((3*a+b)/20 + 2/25) = 13/125 →
      a = 1/5 ∧ b = 3/5) := by
  rcases le_or_gt b a with hab | hab
  · -- no customized sales
    have hQC : max 0 (min 1 b - max 0 a) = 0 := by
      apply max_eq_left
      have : min 1 b ≤ b := min_le_right _ _
      have : a ≤ max 0 a := le_max_right _ _
      linarith
    have hm : max ((3*a+b)/4) b = (3*a+b)/4 := max_eq_left (by linarith)
    have hm0 : max 0 ((3*a+b)/4) = (3*a+b)/4 := max_eq_right (by linarith)
    rw [hQC, hm, hm0]
    have key : max 0 (1 - (3*a+b)/4) * ((3*a+b)/20 + 2/25) < 13/125 := by
      rcases le_or_gt (1 - (3*a+b)/4) 0 with h | h
      · rw [max_eq_left h]; norm_num
      · rw [max_eq_right h.le]; nlinarith [sq_nonneg ((3*a+b)/4 - 3/10)]
    constructor
    · linarith
    · intro h; linarith
  · have hm : max ((3*a+b)/4) b = b := max_eq_right (by linarith)
    rw [hm]
    rcases le_or_gt b 0 with hb0 | hb0
    · have hQC : max 0 (min 1 b - max 0 a) = 0 := by
        apply max_eq_left
        have : min 1 b ≤ b := min_le_right _ _
        have : 0 ≤ max 0 a := le_max_left _ _
        linarith
      rw [hQC, max_eq_left hb0, sub_zero, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      constructor
      · nlinarith
      · intro h; nlinarith
    rcases le_or_gt b 1 with hb1 | hb1
    · rw [min_eq_right hb1, max_eq_right hb0.le, max_eq_right (by linarith : (0:ℝ) ≤ 1 - b)]
      rcases le_or_gt a 0 with ha0 | ha0
      · rw [max_eq_left ha0, sub_zero, max_eq_right hb0.le]
        constructor
        · nlinarith [sq_nonneg (b - 3/5)]
        · intro h; nlinarith [sq_nonneg (b - 3/5)]
      · rw [max_eq_right ha0.le, max_eq_right (by linarith : (0:ℝ) ≤ b - a)]
        have hid : (b - a) * (3*a/20+9/100) + (1 - b) * ((3*a+b)/20 + 2/25) =
            13/125 - 3/20*(a-1/5)^2 - 1/20*(b-3/5)^2 := by ring
        rw [hid]
        constructor
        · nlinarith [sq_nonneg (a-1/5), sq_nonneg (b-3/5)]
        · intro h
          have h1 : (a - 1/5)^2 = 0 := by nlinarith [sq_nonneg (a-1/5), sq_nonneg (b-3/5)]
          have h2 : (b - 3/5)^2 = 0 := by nlinarith [sq_nonneg (a-1/5), sq_nonneg (b-3/5)]
          constructor
          · nlinarith [pow_eq_zero_iff (n := 2) (a := a - 1/5) (by norm_num) |>.mp h1]
          · nlinarith [pow_eq_zero_iff (n := 2) (a := b - 3/5) (by norm_num) |>.mp h2]
    · rw [min_eq_left hb1.le, max_eq_right hb0.le, max_eq_left (by linarith : 1 - b ≤ 0),
        zero_mul, add_zero]
      have key : max 0 (1 - max 0 a) * (3*a/20+9/100) < 13/125 := by
        rcases le_or_gt a 0 with ha0 | ha0
        · rw [max_eq_left ha0, sub_zero, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]; linarith
        · rw [max_eq_right ha0.le]
          rcases le_or_gt (1 - a) 0 with h | h
          · rw [max_eq_left h]; norm_num
          · rw [max_eq_right h.le]; nlinarith [sq_nonneg (a - 1/5)]
      constructor
      · linarith
      · intro h; linarith

theorem cf (a : ℝ) (ha : -1 ≤ a) :
    (0 < max 0 (min 1 (6/5-3*a) - max 0 a) →
      max 0 (min 1 (6/5-3*a) - max 0 a) * (3*a/20+1/20) +
      max 0 (1 - max 0 (max ((3*a+(6/5-3*a))/4) (6/5-3*a))) * (7/50) < 49/500) ∧
    (max 0 (min 1 (6/5-3*a) - max 0 a) = 0 →
      max 0 (1 - max 0 (max ((3*a+(6/5-3*a))/4) (6/5-3*a))) = 7/10) := by
  have hc : (3*a+(6/5-3*a))/4 = 3/10 := by ring
  rw [hc]
  rcases le_or_gt (3/10) a with h3 | h3
  · have hQC : max 0 (min 1 (6/5-3*a) - max 0 a) = 0 := by
      apply max_eq_left
      have : min 1 (6/5-3*a) ≤ 6/5-3*a := min_le_right _ _
      have : a ≤ max 0 a := le_max_right _ _
      linarith
    rw [hQC, max_eq_left (by linarith : 6/5-3*a ≤ 3/10), max_eq_right (by norm_num : (0:ℝ) ≤ 3/10),
      max_eq_right (by norm_num : (0:ℝ) ≤ 1 - 3/10)]
    constructor
    · intro h; exact absurd h (lt_irrefl 0)
    · intro _; norm_num
  · rw [max_eq_right (by linarith : 3/10 ≤ 6/5-3*a), max_eq_right (by linarith : (0:ℝ) ≤ 6/5-3*a)]
    have hpos : 0 < min 1 (6/5-3*a) - max 0 a := by
      have : 3/10 < min 1 (6/5-3*a) := lt_min (by norm_num) (by linarith)
      have : max 0 a < 3/10 := max_lt (by norm_num) h3
      linarith
    rw [max_eq_right hpos.le]
    refine ⟨fun _ => ?_, fun h => absurd h hpos.ne'⟩
    rcases le_or_gt (6/5-3*a) 1 with hb1 | hb1
    · rw [min_eq_right hb1, max_eq_right (by linarith : (0:ℝ) ≤ 1 - (6/5-3*a))]
      have ha0 : 0 < a := by linarith
      rw [max_eq_right ha0.le]
      nlinarith
    · rw [min_eq_left hb1.le, max_eq_left (by linarith : 1 - (6/5-3*a) ≤ 0), zero_mul, add_zero]
      rcases le_or_gt a 0 with ha0 | ha0
      · rw [max_eq_left ha0]; linarith
      · rw [max_eq_right ha0.le]; nlinarith


noncomputable def P0 : Params := ⟨-1/2, 3/4, 0, 3/5, 1/5, 1/10, 0, 1/10, 1/10⟩

noncomputable def Ec (x : Policy) : ℝ := if x.fc < x.pc then 3/5*x.pc + 2/5*x.fc else x.pc
noncomputable def Es (x : Policy) : ℝ := if x.fs < x.ps then 1/5*x.ps + 4/5*x.fs else x.ps

theorem standing : P0.Standing := by
  simp only [Params.Standing, Params.μc, Params.μs, P0]
  norm_num

theorem Ec_nonneg (x : Policy) (hx : x.Feasible) : 0 ≤ Ec x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  unfold Ec; split_ifs <;> positivity

theorem Es_nonneg (x : Policy) (hx : x.Feasible) : 0 ≤ Es x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  unfold Es; split_ifs <;> positivity

theorem euC_cases (x : Policy) (hx : x.Feasible) (t : ℝ) :
    euC P0 x t = 3/20 + 3/20*t - Ec x ∨ (euC P0 x t ≤ 0 ∧ 3/20 + 3/20*t - Ec x ≤ 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [euC, wtpC, P0, Ec, max_def]
  split_ifs <;> first | (left; ring1) | (left; linarith) | (right; constructor <;> nlinarith)

theorem euS_cases (x : Policy) (hx : x.Feasible) (t : ℝ) :
    euS P0 x t = 1/5*t - Es x ∨ (euS P0 x t ≤ 0 ∧ 1/5*t - Es x ≤ 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [euS, wtpS, P0, Es, max_def]
  split_ifs <;> first | (left; ring1) | (left; linarith) | (right; constructor <;> nlinarith)

theorem buysC_iff (x : Policy) (hx : x.Feasible) (t : ℝ) :
    buysC P0 x t ↔ (0 < 3/20 + 3/20*t - Ec x ∧ 1/5*t - Es x < 3/20 + 3/20*t - Ec x) := by
  rcases euC_cases x hx t with hc | ⟨hc1, hc2⟩ <;>
    rcases euS_cases x hx t with hs | ⟨hs1, hs2⟩ <;> simp only [buysC] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem buysS_iff (x : Policy) (hx : x.Feasible) (t : ℝ) :
    buysS P0 x t ↔ (0 < 1/5*t - Es x ∧ 3/20 + 3/20*t - Ec x ≤ 1/5*t - Es x) := by
  rcases euC_cases x hx t with hc | ⟨hc1, hc2⟩ <;>
    rcases euS_cases x hx t with hs | ⟨hs1, hs2⟩ <;> simp only [buysS] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem returnsC_iff (x : Policy) (t : ℝ) : returnsC P0 x t ↔ x.fc < x.pc := by
  simp only [returnsC, P0, zero_mul, zero_sub]
  constructor <;> intro h <;> linarith

theorem returnsS_iff (x : Policy) (t : ℝ) : returnsS P0 x t ↔ x.fs < x.ps := by
  simp only [returnsS, P0, zero_mul, zero_sub]
  constructor <;> intro h <;> linarith

theorem vol1 (a b : ℝ) :
    (volume {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ a < t ∧ t < b}).toReal = max 0 (min 1 b - max 0 a) := by
  have h1 : Ioo (max 0 a) (min 1 b) ⊆ {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ a < t ∧ t < b} := by
    intro t ⟨ht1, ht2⟩
    rw [max_lt_iff] at ht1; rw [lt_min_iff] at ht2
    exact ⟨⟨ht1.1.le, ht2.1.le⟩, ht1.2, ht2.2⟩
  have h2 : {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ a < t ∧ t < b} ⊆ Icc (max 0 a) (min 1 b) := by
    rintro t ⟨⟨h0, h1⟩, ha, hb⟩
    exact ⟨max_le h0 ha.le, le_min h1 hb.le⟩
  have hv : volume {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ a < t ∧ t < b} = ENNReal.ofReal (min 1 b - max 0 a) := by
    apply le_antisymm
    · calc _ ≤ volume (Icc (max 0 a) (min 1 b)) := measure_mono h2
        _ = _ := Real.volume_Icc
    · calc ENNReal.ofReal (min 1 b - max 0 a) = volume (Ioo (max 0 a) (min 1 b)) := Real.volume_Ioo.symm
        _ ≤ _ := measure_mono h1
  rw [hv, ENNReal.toReal_ofReal', max_comm]

theorem vol2 (c b : ℝ) :
    (volume {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ c < t ∧ b ≤ t}).toReal = max 0 (1 - max 0 (max c b)) := by
  have h1 : Ioo (max 0 (max c b)) 1 ⊆ {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ c < t ∧ b ≤ t} := by
    intro t ⟨ht1, ht2⟩
    rw [max_lt_iff, max_lt_iff] at ht1
    exact ⟨⟨ht1.1.le, ht2.le⟩, ht1.2.1, ht1.2.2.le⟩
  have h2 : {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ c < t ∧ b ≤ t} ⊆ Icc (max 0 (max c b)) 1 := by
    rintro t ⟨⟨h0, h1⟩, hc, hb⟩
    exact ⟨max_le h0 (max_le hc.le hb), h1⟩
  have hv : volume {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ c < t ∧ b ≤ t} =
      ENNReal.ofReal (1 - max 0 (max c b)) := by
    apply le_antisymm
    · calc _ ≤ volume (Icc (max 0 (max c b)) 1) := measure_mono h2
        _ = _ := Real.volume_Icc
    · calc ENNReal.ofReal (1 - max 0 (max c b)) = volume (Ioo (max 0 (max c b)) 1) :=
            Real.volume_Ioo.symm
        _ ≤ _ := measure_mono h1
  rw [hv, ENNReal.toReal_ofReal', max_comm]

theorem QC_eq (x : Policy) (hx : x.Feasible) :
    QC P0 x = max 0 (min 1 (3 + 20 * Es x - 20 * Ec x) - max 0 (20/3 * Ec x - 1)) := by
  rw [← vol1]
  unfold QC
  congr 2
  ext t
  simp only [mem_setOf_eq, buysC_iff x hx t]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨h0, ?_, ?_⟩ <;> linarith

theorem QS_eq (x : Policy) (hx : x.Feasible) :
    QS P0 x = max 0 (1 - max 0 (max (5 * Es x) (3 + 20 * Es x - 20 * Ec x))) := by
  rw [← vol2]
  unfold QS
  congr 2
  ext t
  simp only [mem_setOf_eq, buysS_iff x hx t]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨h0, ?_, ?_⟩ <;> linarith

theorem QRC_eq (x : Policy) : QRC P0 x = if x.fc < x.pc then QC P0 x else 0 := by
  unfold QRC QC
  by_cases h : x.fc < x.pc
  · rw [if_pos h]
    congr 2; ext t; simp only [mem_setOf_eq, returnsC_iff, h, and_true]
  · rw [if_neg h]
    have : {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ buysC P0 x t ∧ returnsC P0 x t} = ∅ := by
      ext t; simp only [mem_setOf_eq, returnsC_iff, h, and_false, mem_empty_iff_false]
    rw [this]; simp

theorem QRS_eq (x : Policy) : QRS P0 x = if x.fs < x.ps then QS P0 x else 0 := by
  unfold QRS QS
  by_cases h : x.fs < x.ps
  · rw [if_pos h]
    congr 2; ext t; simp only [mem_setOf_eq, returnsS_iff, h, and_true]
  · rw [if_neg h]
    have : {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ buysS P0 x t ∧ returnsS P0 x t} = ∅ := by
      ext t; simp only [mem_setOf_eq, returnsS_iff, h, and_false, mem_empty_iff_false]
    rw [this]; simp

theorem profit_eq (x : Policy) :
    profit P0 x = QC P0 x * (Ec x - 1/10 + (if x.fc < x.pc then 1/25 else 0)) +
      QS P0 x * (Es x + (if x.fs < x.ps then 2/25 else 0)) := by
  simp only [profit, RC, RS]
  rw [QRC_eq, QRS_eq]
  simp only [Ec, Es, P0]
  split_ifs <;> ring

theorem QC_nonneg (x : Policy) : 0 ≤ QC P0 x := ENNReal.toReal_nonneg
theorem QS_nonneg (x : Policy) : 0 ≤ QS P0 x := ENNReal.toReal_nonneg

theorem core' (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    max 0 (min 1 (3 + 20 * F - 20 * E) - max 0 (20/3 * E - 1)) * (E - 3/50) +
      max 0 (1 - max 0 (max (5 * F) (3 + 20 * F - 20 * E))) * (F + 2/25) ≤ 13/125 ∧
    (max 0 (min 1 (3 + 20 * F - 20 * E) - max 0 (20/3 * E - 1)) * (E - 3/50) +
      max 0 (1 - max 0 (max (5 * F) (3 + 20 * F - 20 * E))) * (F + 2/25) = 13/125 →
      E = 9/50 ∧ F = 3/50) := by
  have h := core (20/3*E-1) (3 + 20 * F - 20 * E) (by linarith) (by linarith)
  have e1 : 3*(20/3*E-1)/20+9/100 = E - 3/50 := by ring
  have e2 : (3*(20/3*E-1) + (3 + 20 * F - 20 * E))/4 = 5 * F := by ring
  have e3 : (3*(20/3*E-1) + (3 + 20 * F - 20 * E))/20 + 2/25 = F + 2/25 := by ring
  rw [e1, e2, e3] at h
  refine ⟨h.1, fun heq => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 heq
  constructor <;> linarith

theorem cf' (E : ℝ) (hE : 0 ≤ E) :
    (0 < max 0 (min 1 (3 + 20 * (3/50) - 20 * E) - max 0 (20/3 * E - 1)) →
      max 0 (min 1 (3 + 20 * (3/50) - 20 * E) - max 0 (20/3 * E - 1)) * (E - 1/10) +
      max 0 (1 - max 0 (max (5 * (3/50)) (3 + 20 * (3/50) - 20 * E))) * (7/50) < 49/500) ∧
    (max 0 (min 1 (3 + 20 * (3/50) - 20 * E) - max 0 (20/3 * E - 1)) = 0 →
      max 0 (1 - max 0 (max (5 * (3/50)) (3 + 20 * (3/50) - 20 * E))) = 7/10) := by
  have h := cf (20/3*E-1) (by linarith)
  have e0 : (6/5 - 3*(20/3*E-1)) = 3 + 20 * (3/50) - 20 * E := by ring
  have e1 : 3*(20/3*E-1)/20+1/20 = E - 1/10 := by ring
  have e2 : (3*(20/3*E-1) + (3 + 20 * (3/50) - 20 * E))/4 = 5 * (3/50) := by ring
  rw [e0, e1, e2] at h
  exact h

theorem profit_le (y : Policy) (hy : y.Feasible) : profit P0 y ≤ 13/125 := by
  have hb := (core' (Ec y) (Es y) (Ec_nonneg y hy) (Es_nonneg y hy)).1
  rw [← QC_eq y hy, ← QS_eq y hy] at hb
  rw [profit_eq]
  have h1 : QC P0 y * (Ec y - 1/10 + (if y.fc < y.pc then 1/25 else 0)) ≤ QC P0 y * (Ec y - 3/50) := by
    apply mul_le_mul_of_nonneg_left _ (QC_nonneg y); split_ifs <;> linarith
  have h2 : QS P0 y * (Es y + (if y.fs < y.ps then 2/25 else 0)) ≤ QS P0 y * (Es y + 2/25) := by
    apply mul_le_mul_of_nonneg_left _ (QS_nonneg y); split_ifs <;> linarith
  linarith

noncomputable def xstar : Policy := ⟨3/10, 3/10, 0, 0⟩

theorem xstar_feas : xstar.Feasible := by
  simp only [Policy.Feasible, xstar]; norm_num

theorem Ec_xstar : Ec xstar = 9/50 := by simp only [Ec, xstar]; norm_num
theorem Es_xstar : Es xstar = 3/50 := by simp only [Es, xstar]; norm_num

theorem profit_xstar : profit P0 xstar = 13/125 := by
  rw [profit_eq, QC_eq _ xstar_feas, QS_eq _ xstar_feas, Ec_xstar, Es_xstar]
  simp only [xstar]
  norm_num

end CRSol

open CustomReturns.WinWin CRSol in
theorem solution :
    ∃ P : Params, P.Standing ∧ (∃ x : Policy, IsOptimal P x) ∧
      ∀ x : Policy, IsOptimal P x →
        0 < RC P x ∧
        (∃ y : Policy, IsOptimalNoCReturns P x y) ∧
        ∀ y : Policy, IsOptimalNoCReturns P x y →
          profit P y < profit P x ∧ totalReturns P x < totalReturns P y := by
  refine ⟨P0, standing, ⟨xstar, xstar_feas, fun y hy => profit_xstar ▸ profit_le y hy⟩, ?_⟩
  intro x ⟨hx, hopt⟩
  have hpx : profit P0 x = 13/125 :=
    le_antisymm (profit_le x hx) (profit_xstar ▸ hopt xstar xstar_feas)
  -- characterize the optimum
  have hcore := core' (Ec x) (Es x) (Ec_nonneg x hx) (Es_nonneg x hx)
  rw [← QC_eq x hx, ← QS_eq x hx] at hcore
  have hpe := profit_eq x
  have hupper : QC P0 x * (Ec x - 3/50) + QS P0 x * (Es x + 2/25) = 13/125 := by
    have h1 : QC P0 x * (Ec x - 1/10 + (if x.fc < x.pc then 1/25 else 0)) ≤ QC P0 x * (Ec x - 3/50) := by
      apply mul_le_mul_of_nonneg_left _ (QC_nonneg x); split_ifs <;> linarith
    have h2 : QS P0 x * (Es x + (if x.fs < x.ps then 2/25 else 0)) ≤ QS P0 x * (Es x + 2/25) := by
      apply mul_le_mul_of_nonneg_left _ (QS_nonneg x); split_ifs <;> linarith
    linarith [hcore.1]
  obtain ⟨hE, hF⟩ := hcore.2 hupper
  have hQC : QC P0 x = 2/5 := by rw [QC_eq x hx, hE, hF]; norm_num
  have hQS : QS P0 x = 2/5 := by rw [QS_eq x hx, hE, hF]; norm_num
  have hon_c : x.fc < x.pc := by
    by_contra h
    rw [if_neg h, hQC, hE] at hpe
    have : (if x.fs < x.ps then (2:ℝ)/25 else 0) ≤ 2/25 := by split_ifs <;> linarith
    rw [hQS, hF] at hpe
    nlinarith
  have hon_s : x.fs < x.ps := by
    by_contra h
    rw [if_neg h, hQS, hF, hQC, hE] at hpe
    have : (if x.fc < x.pc then (1:ℝ)/25 else 0) ≤ 1/25 := by split_ifs <;> linarith
    nlinarith
  have hRC : RC P0 x = 4/25 := by
    rw [RC, QRC_eq, if_pos hon_c, hQC]; simp only [P0]; norm_num
  have hRS : RS P0 x = 8/25 := by
    rw [RS, QRS_eq, if_pos hon_s, hQS]; simp only [P0]; norm_num
  have hEsy : ∀ y : Policy, y.ps = x.ps → y.fs = x.fs → Es y = 3/50 := by
    intro y h1 h2; rw [← hF]; simp only [Es, h1, h2]
  -- counterfactual bound
  have cfbound : ∀ z : Policy, z.Feasible → z.ps = x.ps → z.fs = x.fs → RC P0 z = 0 →
      profit P0 z ≤ 49/500 ∧ (49/500 ≤ profit P0 z → QC P0 z = 0 ∧ QS P0 z = 7/10) := by
    intro z hz h1 h2 hrc
    have hEz := hEsy z h1 h2
    have hsz : z.fs < z.ps := by rw [h1, h2]; exact hon_s
    have hcf := cf' (Ec z) (Ec_nonneg z hz)
    rw [← hEz, ← QC_eq z hz, ← QS_eq z hz] at hcf
    have hpz := profit_eq z
    rw [if_pos hsz, hEz] at hpz
    have hQRC0 : QRC P0 z = 0 := by
      simp only [RC, P0] at hrc
      rcases mul_eq_zero.mp hrc with h | h
      · norm_num at h
      · exact h
    rcases (QC_nonneg z).lt_or_eq with hpos | hzero
    · -- customized sales are positive, so customized returns are off
      have hoff : ¬ z.fc < z.pc := by
        intro hc; rw [QRC_eq, if_pos hc] at hQRC0; linarith
      rw [if_neg hoff] at hpz
      have hlt := hcf.1 hpos
      have : profit P0 z < 49/500 := by rw [hpz]; linarith
      exact ⟨this.le, fun h => absurd h (not_le.mpr this)⟩
    · have hQS7 := hcf.2 hzero.symm
      refine ⟨?_, fun _ => ⟨hzero.symm, hQS7⟩⟩
      rw [hpz, ← hzero, hQS7]; norm_num
  -- the explicit counterfactual policy
  set y0 : Policy := ⟨1, x.ps, 1, x.fs⟩ with hy0
  have hy0f : y0.Feasible := ⟨by norm_num, hx.2.1, by norm_num, hx.2.2.2⟩
  have hRCy0 : RC P0 y0 = 0 := by
    simp only [RC, QRC_eq, hy0, lt_irrefl, if_false, mul_zero]
  have hpy0 : profit P0 y0 = 49/500 := by
    have hEc : Ec y0 = 1 := by simp [Ec, hy0]
    have hEs : Es y0 = 3/50 := hEsy y0 rfl rfl
    have hsz : y0.fs < y0.ps := hon_s
    rw [profit_eq, if_pos hsz, QC_eq y0 hy0f, QS_eq y0 hy0f, hEc, hEs]
    norm_num
  refine ⟨by rw [hRC]; norm_num, ⟨y0, hy0f, rfl, rfl, hRCy0, fun z hz h1 h2 h3 => ?_⟩, ?_⟩
  · rw [hpy0]; exact (cfbound z hz h1 h2 h3).1
  · rintro y ⟨hyf, h1, h2, hrc, hyopt⟩
    have hge : 49/500 ≤ profit P0 y := hpy0 ▸ hyopt y0 hy0f rfl rfl hRCy0
    obtain ⟨hle, hchar⟩ := cfbound y hyf h1 h2 hrc
    obtain ⟨hQCy, hQSy⟩ := hchar hge
    have hsy : y.fs < y.ps := by rw [h1, h2]; exact hon_s
    have hRSy : RS P0 y = 14/25 := by
      rw [RS, QRS_eq, if_pos hsy, hQSy]; simp only [P0]; norm_num
    refine ⟨by rw [hpx]; linarith, ?_⟩
    simp only [totalReturns]
    rw [hRC, hRS, hrc, hRSy]; norm_num
