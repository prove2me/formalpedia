-- Prove2me | solution 1 for BOGOPromo.NoStockpile.pr_profit_eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:44:43.633795+00:00
-- url     : https://prove2.me/submissions/5cf59aec-8201-455a-a505-8e6cd5b82ab1

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

set_option autoImplicit false

namespace BOGOPromo.NoStockpile.Aux

open MeasureTheory BOGOPromo.NoStockpile

/-! ### Step indicators on `[0,1]` -/

/-- `1(p ≤ v)` -/
noncomputable def ind (p v : ℝ) : ℝ := if p ≤ v then 1 else 0

/-- Length of `[p,1] ∩ [0,1]` for `p ≥ 0`. -/
noncomputable def L (p : ℝ) : ℝ := max (1 - p) 0

lemma ind_mono (p : ℝ) : Monotone (ind p) := by
  intro x y hxy
  unfold ind
  split_ifs with h1 h2 <;> first | (exfalso; linarith) | norm_num

lemma ind_ii (p : ℝ) : IntervalIntegrable (ind p) volume 0 1 :=
  (ind_mono p).intervalIntegrable

lemma int_ind (p : ℝ) (hp : 0 ≤ p) : ∫ v in (0:ℝ)..1, ind p v = L p := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have : (fun v : ℝ => ind p v) = (Set.Ici p).indicator (fun _ => (1:ℝ)) := by
    ext v; simp [ind, Set.indicator]
  rw [this, setIntegral_indicator measurableSet_Ici, setIntegral_const]
  have hv : volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ici p) = ENNReal.ofReal (max (1 - p) 0) := by
    rcases le_or_gt p 1 with h | h
    · rw [max_eq_left (by linarith)]
      apply le_antisymm
      · calc volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ici p) ≤ volume (Set.Icc p 1) := by
              apply measure_mono
              intro v hv; exact ⟨hv.2, hv.1.2⟩
          _ = ENNReal.ofReal (1 - p) := Real.volume_Icc
      · calc ENNReal.ofReal (1 - p) = volume (Set.Ioc p 1) := Real.volume_Ioc.symm
          _ ≤ _ := by
              apply measure_mono
              intro v hv; exact ⟨⟨by linarith [hv.1], hv.2⟩, le_of_lt hv.1⟩
    · rw [max_eq_right (by linarith)]
      have : Set.Ioc (0:ℝ) 1 ∩ Set.Ici p = ∅ := by
        ext v; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; linarith [h1.2]
      rw [this]; simp
  rw [Measure.real, hv, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul, mul_one]
  rfl

/-- Integral of a combination of three step indicators. -/
lemma int_comb3 (a b c p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ∫ v in (0:ℝ)..1, (a * ind p v + b * ind q v + c * ind r v) = a * L p + b * L q + c * L r := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, int_ind p hp, int_ind q hq, int_ind r hr]
  · exact (ind_ii p).const_mul a
  · exact (ind_ii q).const_mul b
  · exact ((ind_ii p).const_mul a).add ((ind_ii q).const_mul b)
  · exact (ind_ii r).const_mul c

lemma int_comb4 (a b c d p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ∫ v in (0:ℝ)..1, (a * ind p v + b * ind q v + c * ind r v + d * ind s v) =
      a * L p + b * L q + c * L r + d * L s := by
  rw [intervalIntegral.integral_add, int_comb3 a b c p q r hp hq hr,
    intervalIntegral.integral_const_mul, int_ind s hs]
  · exact (((ind_ii p).const_mul a).add ((ind_ii q).const_mul b)).add ((ind_ii r).const_mul c)
  · exact (ind_ii s).const_mul d

/-! ### Consumer choice -/

lemma forall_BOpt (P : BOpt → Prop) : (∀ o, P o) ↔ P .o00 ∧ P .o11 ∧ P .o20 ∧ P .o21 := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4⟩ o; cases o <;> assumption

lemma forall_POpt (P : POpt → Prop) :
    (∀ o, P o) ↔ P .o00 ∧ P .o10 ∧ P .o11 ∧ P .o20 ∧ P .o21 := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩ o; cases o <;> assumption

lemma bChoice_eq (θ pb pg v : ℝ) :
    bChoice θ pb pg v =
      if pb ≤ v then (if pg ≤ θ * v then .o21 else .o11)
      else (if pb + pg ≤ (1 + θ) * v then .o20 else .o00) := by
  unfold bChoice
  simp only [forall_BOpt, bUtil]
  by_cases h1 : pb ≤ v
  · by_cases h2 : pg ≤ θ * v
    · rw [if_pos h1, if_pos h2, if_pos]
      refine ⟨?_, ?_, ?_, le_refl _⟩ <;> nlinarith
    · rw [if_pos h1, if_neg h2, if_neg, if_neg, if_pos]
      · refine ⟨?_, le_refl _, ?_, ?_⟩ <;> nlinarith
      · intro h; nlinarith [h.2.1]
      · intro h; nlinarith [h.2.1]
  · by_cases h3 : pb + pg ≤ (1 + θ) * v
    · rw [if_neg h1, if_pos h3, if_neg, if_pos]
      · refine ⟨?_, ?_, le_refl _, ?_⟩ <;> nlinarith
      · intro h; nlinarith [h.2.2.1]
    · rw [if_neg h1, if_neg h3, if_neg, if_neg, if_neg]
      · intro h; nlinarith [h.1]
      · intro h; nlinarith [h.1]
      · intro h; nlinarith [h.1]

lemma pChoice_eq (θ pr pd v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpd : 0 ≤ pd) (hdr : pd ≤ pr) :
    pChoice θ pr pd v =
      if pr ≤ v then (if pd ≤ θ * v then .o21 else .o11)
      else (if pd ≤ θ * v then .o20 else (if pd ≤ v then .o10 else .o00)) := by
  unfold pChoice
  simp only [forall_POpt, pUtil]
  by_cases hA : pr ≤ v
  · by_cases hB : pd ≤ θ * v
    · rw [if_pos hA, if_pos hB, if_pos]
      refine ⟨?_, ?_, ?_, ?_, le_refl _⟩ <;> nlinarith
    · rw [if_pos hA, if_neg hB, if_neg, if_neg, if_pos]
      · refine ⟨?_, ?_, le_refl _, ?_, ?_⟩ <;> nlinarith
      · intro h; nlinarith [h.2.2.1]
      · intro h; nlinarith [h.2.2.1]
  · by_cases hB : pd ≤ θ * v
    · rw [if_neg hA, if_pos hB, if_neg, if_pos]
      · refine ⟨?_, ?_, ?_, le_refl _, ?_⟩ <;> nlinarith
      · intro h; nlinarith [h.2.2.2.1]
    · by_cases hC : pd ≤ v
      · rw [if_neg hA, if_neg hB, if_pos hC, if_neg, if_neg, if_neg, if_pos]
        · refine ⟨?_, le_refl _, ?_, ?_, ?_⟩ <;> nlinarith
        · intro h; nlinarith [h.2.1]
        · intro h; nlinarith [h.2.1]
        · intro h; nlinarith [h.2.1]
      · rw [if_neg hA, if_neg hB, if_neg hC, if_neg, if_neg, if_neg, if_neg]
        · intro h; nlinarith [h.1]
        · intro h; nlinarith [h.1]
        · intro h; nlinarith [h.1]
        · intro h; nlinarith [h.1]

/-! ### Closed forms -/

lemma bMargin_eq (θ w pb pg v : ℝ) (hθ0 : 0 < θ) :
    bMargin pb pg w (bChoice θ pb pg v) =
      (2 * pb - 2 * w) * ind pb v + (pg - w) * ind (max pb (pg / θ)) v +
      (pb + pg - 2 * w) * ind ((pb + pg) / (1 + θ)) v +
      (-(pb + pg - 2 * w)) * ind (max ((pb + pg) / (1 + θ)) pb) v := by
  have h1θ : 0 < 1 + θ := by linarith
  have e1 : max pb (pg / θ) ≤ v ↔ pb ≤ v ∧ pg ≤ θ * v := by
    rw [max_le_iff, div_le_iff₀ hθ0, mul_comm v θ]
  have e2 : (pb + pg) / (1 + θ) ≤ v ↔ pb + pg ≤ (1 + θ) * v := by
    rw [div_le_iff₀ h1θ, mul_comm v]
  have e3 : max ((pb + pg) / (1 + θ)) pb ≤ v ↔ pb + pg ≤ (1 + θ) * v ∧ pb ≤ v := by
    rw [max_le_iff, e2]
  simp only [ind, e1, e3, e2, bChoice_eq]
  by_cases h1 : pb ≤ v <;> by_cases h2 : pg ≤ θ * v <;> by_cases h3 : pb + pg ≤ (1 + θ) * v <;>
    simp [h1, h2, h3, bMargin] <;> ring

lemma bUnits_eq (θ pb pg v : ℝ) (hθ0 : 0 < θ) :
    bUnits (bChoice θ pb pg v) =
      2 * ind pb v + 1 * ind (max pb (pg / θ)) v +
      2 * ind ((pb + pg) / (1 + θ)) v + (-2) * ind (max ((pb + pg) / (1 + θ)) pb) v := by
  have h1θ : 0 < 1 + θ := by linarith
  have e1 : max pb (pg / θ) ≤ v ↔ pb ≤ v ∧ pg ≤ θ * v := by
    rw [max_le_iff, div_le_iff₀ hθ0, mul_comm v θ]
  have e2 : (pb + pg) / (1 + θ) ≤ v ↔ pb + pg ≤ (1 + θ) * v := by
    rw [div_le_iff₀ h1θ, mul_comm v]
  have e3 : max ((pb + pg) / (1 + θ)) pb ≤ v ↔ pb + pg ≤ (1 + θ) * v ∧ pb ≤ v := by
    rw [max_le_iff, e2]
  simp only [ind, e1, e3, e2, bChoice_eq]
  by_cases h1 : pb ≤ v <;> by_cases h2 : pg ≤ θ * v <;> by_cases h3 : pb + pg ≤ (1 + θ) * v <;>
    simp [h1, h2, h3, bUnits] <;> norm_num

lemma bogoProfit_eq (θ w pb pg : ℝ) (hθ0 : 0 < θ) (hpb : 0 ≤ pb) (hpg : 0 ≤ pg) :
    bogoProfit θ w pb pg =
      (2 * pb - 2 * w) * L pb + (pg - w) * L (max pb (pg / θ)) +
      (pb + pg - 2 * w) * (L ((pb + pg) / (1 + θ)) - L (max ((pb + pg) / (1 + θ)) pb)) := by
  have h1θ : 0 < 1 + θ := by linarith
  unfold bogoProfit
  simp_rw [bMargin_eq θ w pb pg _ hθ0]
  rw [int_comb4 _ _ _ _ _ _ _ _ hpb (le_max_of_le_left hpb) (by positivity)
    (le_max_of_le_right hpb)]
  ring

lemma bogoDemand_eq (θ pb pg : ℝ) (hθ0 : 0 < θ) (hpb : 0 ≤ pb) (hpg : 0 ≤ pg) :
    bogoDemand θ pb pg =
      2 * L pb + L (max pb (pg / θ)) +
      2 * (L ((pb + pg) / (1 + θ)) - L (max ((pb + pg) / (1 + θ)) pb)) := by
  have h1θ : 0 < 1 + θ := by linarith
  unfold bogoDemand
  simp_rw [bUnits_eq θ pb pg _ hθ0]
  rw [int_comb4 _ _ _ _ _ _ _ _ hpb (le_max_of_le_left hpb) (by positivity)
    (le_max_of_le_right hpb)]
  ring

lemma pMargin_eq (θ w pr pd v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpd : 0 ≤ pd) (hdr : pd ≤ pr) :
    pMargin pr pd w (pChoice θ pr pd v) =
      (pd - w) * ind pd v + (pr - w) * ind pr v + (pd - w) * ind (pd / θ) v := by
  have e1 : pd / θ ≤ v ↔ pd ≤ θ * v := by rw [div_le_iff₀ hθ0, mul_comm v θ]
  simp only [ind, e1, pChoice_eq θ pr pd v hθ0 hθ1 hpd hdr]
  by_cases h1 : pr ≤ v <;> by_cases h2 : pd ≤ θ * v <;> by_cases h3 : pd ≤ v
  all_goals first
    | (exfalso; nlinarith)
    | (simp [h1, h2, h3, pMargin]; try ring)

lemma pUnits_eq (θ pr pd v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpd : 0 ≤ pd) (hdr : pd ≤ pr) :
    pUnits (pChoice θ pr pd v) = 1 * ind pd v + 1 * ind pr v + 1 * ind (pd / θ) v := by
  have e1 : pd / θ ≤ v ↔ pd ≤ θ * v := by rw [div_le_iff₀ hθ0, mul_comm v θ]
  simp only [ind, e1, pChoice_eq θ pr pd v hθ0 hθ1 hpd hdr]
  by_cases h1 : pr ≤ v <;> by_cases h2 : pd ≤ θ * v <;> by_cases h3 : pd ≤ v
  all_goals first
    | (exfalso; nlinarith)
    | (simp [h1, h2, h3, pUnits]; try norm_num)

lemma prProfit_eq (θ w pr pd : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpd : 0 ≤ pd) (hdr : pd ≤ pr) :
    prProfit θ w pr pd = (pd - w) * L pd + (pr - w) * L pr + (pd - w) * L (pd / θ) := by
  unfold prProfit
  simp_rw [pMargin_eq θ w pr pd _ hθ0 hθ1 hpd hdr]
  exact int_comb3 _ _ _ _ _ _ hpd (by linarith) (by positivity)

lemma prDemand_eq (θ pr pd : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hpd : 0 ≤ pd) (hdr : pd ≤ pr) :
    prDemand θ pr pd = L pd + L pr + L (pd / θ) := by
  unfold prDemand
  simp_rw [pUnits_eq θ pr pd _ hθ0 hθ1 hpd hdr]
  rw [int_comb3 _ _ _ _ _ _ hpd (by linarith) (by positivity)]
  ring

lemma ind_int_np (w p : ℝ) (hp : 0 ≤ p) : npProfit w p = 2 * (p - w) * L p := by
  unfold npProfit
  have : (fun v : ℝ => if p ≤ v then 2 * (p - w) else 0) =
      fun v => 2 * (p - w) * ind p v := by
    ext v; simp [ind]
  rw [this, intervalIntegral.integral_const_mul, int_ind p hp]

lemma ind_int_npD (p : ℝ) (hp : 0 ≤ p) : npDemand p = 2 * L p := by
  unfold npDemand
  have : (fun v : ℝ => if p ≤ v then (2:ℝ) else 0) = fun v => 2 * ind p v := by
    ext v; simp [ind]
  rw [this, intervalIntegral.integral_const_mul, int_ind p hp]

end BOGOPromo.NoStockpile.Aux

open BOGOPromo.NoStockpile BOGOPromo.NoStockpile.Aux

theorem solution (θ w pr pd : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hpd0 : 0 ≤ pd) (hpdr : pd ≤ pr) (hpr1 : pr ≤ 1) (hpdθ : pd ≤ θ) :
    prProfit θ w pr pd = (1 - pr) * (pr - w) + (2 - pd - pd / θ) * (pd - w) ∧
    prDemand θ pr pd = (1 - pr) + (2 - pd - pd / θ) := by
  have eL1 : L pd = 1 - pd := max_eq_left (by linarith)
  have eL2 : L pr = 1 - pr := max_eq_left (by linarith)
  have hq1 : pd / θ ≤ 1 := by rw [div_le_one hθ0]; exact hpdθ
  have eL3 : L (pd / θ) = 1 - pd / θ := max_eq_left (by linarith)
  rw [prProfit_eq θ w pr pd hθ0 hθ1 hpd0 hpdr, prDemand_eq θ pr pd hθ0 hθ1 hpd0 hpdr, eL1, eL2, eL3]
  constructor <;> ring
