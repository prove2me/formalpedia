-- Prove2me | solution 1 for BOGOPromo.NoStockpile.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:03:19.787311+00:00
-- url     : https://prove2.me/submissions/243ea714-a212-4f99-8db6-dad65472703d

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

/-! ### Basic facts on `L` -/

lemma L_nonneg (p : ℝ) : 0 ≤ L p := le_max_right _ _

lemma L_of_le (p : ℝ) (h : p ≤ 1) : L p = 1 - p := max_eq_left (by linarith)

lemma L_of_ge (p : ℝ) (h : 1 ≤ p) : L p = 0 := max_eq_right (by linarith)

lemma L_anti {p q : ℝ} (h : p ≤ q) : L q ≤ L p := max_le_max (by linarith) le_rfl

/-- `2 (p - w) L(p) ≤ (1 - w)^2 / 2`. -/
lemma np_le (w p : ℝ) (hw1 : w ≤ 1) : 2 * (p - w) * L p ≤ (1 - w) ^ 2 / 2 := by
  rcases le_or_gt p 1 with h | h
  · rw [L_of_le p h]; nlinarith [sq_nonneg (1 + w - 2 * p)]
  · rw [L_of_ge p h.le]; nlinarith [sq_nonneg (1 - w)]

/-- `(p - w) L(p) ≤ (1 - w)^2 / 4`. -/
lemma half_le (w p : ℝ) (hw1 : w ≤ 1) : (p - w) * L p ≤ (1 - w) ^ 2 / 4 := by
  have := np_le w p hw1; nlinarith

/-- The BOGO-game value: `(1-w)^2/2 + (max (θ - w) 0)^2 / (4θ)`. -/
noncomputable def V1 (θ w : ℝ) : ℝ := (1 - w) ^ 2 / 2 + (max (θ - w) 0) ^ 2 / (4 * θ)

lemma V1_ge (θ w : ℝ) (hθ0 : 0 < θ) : (1 - w) ^ 2 / 2 ≤ V1 θ w := by
  unfold V1; have : 0 ≤ (max (θ - w) 0) ^ 2 / (4 * θ) := by positivity
  linarith

lemma V1_gt (θ w : ℝ) (hθ0 : 0 < θ) (hw : w < θ) : (1 - w) ^ 2 / 2 < V1 θ w := by
  unfold V1; rw [max_eq_left (by linarith)]
  have : 0 < (θ - w) ^ 2 / (4 * θ) := by
    have : 0 < θ - w := by linarith
    positivity
  linarith

/-- `(g - w) L(g/θ) ≤ (max (θ - w) 0)^2 / (4θ)`. -/
lemma second_le (θ w g : ℝ) (hθ0 : 0 < θ) (hg : 0 ≤ g) :
    (g - w) * L (g / θ) ≤ (max (θ - w) 0) ^ 2 / (4 * θ) := by
  rcases le_or_gt g θ with h | h
  · have hq : g / θ ≤ 1 := by rw [div_le_one hθ0]; exact h
    rw [L_of_le _ hq]
    have e : (g - w) * (1 - g / θ) = (g - w) * (θ - g) / θ := by field_simp
    rw [e, div_le_div_iff₀ hθ0 (by positivity)]
    rcases le_or_gt w θ with hw | hw
    · rw [max_eq_left (by linarith)]
      nlinarith [sq_nonneg (θ + w - 2 * g)]
    · rw [max_eq_right (by linarith)]
      have : (g - w) * (θ - g) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      nlinarith
  · have hq : 1 ≤ g / θ := by rw [le_div_iff₀ hθ0]; linarith
    rw [L_of_ge _ hq]; simp; positivity

lemma second_lt (θ w g : ℝ) (hθ0 : 0 < θ) (hg : 0 ≤ g) (hw : w < θ) (hne : g ≠ (θ + w) / 2) :
    (g - w) * L (g / θ) < (max (θ - w) 0) ^ 2 / (4 * θ) := by
  rw [max_eq_left (by linarith)]
  rcases le_or_gt g θ with h | h
  · have hq : g / θ ≤ 1 := by rw [div_le_one hθ0]; exact h
    rw [L_of_le _ hq]
    have e : (g - w) * (1 - g / θ) = (g - w) * (θ - g) / θ := by field_simp
    rw [e, div_lt_div_iff₀ hθ0 (by positivity)]
    have : 0 < (θ + w - 2 * g) ^ 2 := by
      have : θ + w - 2 * g ≠ 0 := by intro h'; apply hne; linarith
      positivity
    nlinarith
  · have hq : 1 ≤ g / θ := by rw [le_div_iff₀ hθ0]; linarith
    rw [L_of_ge _ hq]; simp
    have : 0 < θ - w := by linarith
    positivity

/-- The Case-A boundary value `(1 - x)((2+θ)x - 3w) ≤ V1`. -/
lemma CA_le (θ w x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw1 : w ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) * ((2 + θ) * x - 3 * w) ≤ V1 θ w := by
  have h1 := np_le w x hw1
  have h2 := second_le θ w (θ * x) hθ0 (by positivity)
  rw [L_of_le x hx1] at h1
  have e : θ * x / θ = x := by field_simp
  rw [e, L_of_le x hx1] at h2
  unfold V1; nlinarith

/-- Case B, `a ≤ 1`. -/
lemma caseB1_lt (θ w a g : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hg0 : 0 ≤ g) (hga : g < θ * a) (ha1 : a ≤ 1) :
    (1 - a) * (a - w) + (1 - (a + g) / (1 + θ)) * (a + g - 2 * w) < V1 θ w := by
  have h1θ : 0 < 1 + θ := by linarith
  set t := (a + g) / (1 + θ) with ht
  have hst : a + g = (1 + θ) * t := by rw [ht]; field_simp
  rw [hst]
  have hta : t < a := by rw [ht, div_lt_iff₀ h1θ]; linarith
  have ha0 : 0 < a := by nlinarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  set t0 := 1 / 2 + w / (1 + θ) with ht0d
  have ht0w : (1 + w) / 2 ≤ t0 := by
    rw [ht0d]
    have : w / 2 ≤ w / (1 + θ) := by
      apply div_le_div_of_nonneg_left hw0 h1θ (by linarith)
    linarith
  have key : ∀ x y : ℝ, (1 - x) * ((1 + θ) * x - 2 * w) - (1 - y) * ((1 + θ) * y - 2 * w) =
      (x - y) * (1 + θ) * (2 * t0 - x - y) := by
    intro x y; rw [ht0d]; field_simp; ring
  rcases le_or_gt a t0 with h | h
  · have hφ : (1 - t) * ((1 + θ) * t - 2 * w) < (1 - a) * ((1 + θ) * a - 2 * w) := by
      have := key a t
      have : 0 < (a - t) * (1 + θ) * (2 * t0 - a - t) := by
        apply mul_pos (mul_pos (by linarith) h1θ); linarith
      linarith
    have hCA := CA_le θ w a hθ0 hθ1 hw1 ha0.le ha1
    nlinarith
  · have hφ : (1 - t) * ((1 + θ) * t - 2 * w) ≤ (1 - t0) * ((1 + θ) * t0 - 2 * w) := by
      have := key t0 t
      have : 0 ≤ (t0 - t) ^ 2 * (1 + θ) := by positivity
      nlinarith
    have hfirst : (1 - a) * (a - w) < (1 - t0) * (t0 - w) := by nlinarith
    have ht01 : t0 ≤ 1 := by linarith
    have hCA := CA_le θ w t0 hθ0 hθ1 hw1 (by linarith) ht01
    nlinarith

/-- Case B, `a > 1`. -/
lemma caseB2_le (θ w a g : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hg0 : 0 ≤ g) (ha1 : 1 < a) :
    (a + g - 2 * w) * L ((a + g) / (1 + θ)) ≤ (1 - w) ^ 2 / 2 := by
  have h1θ : 0 < 1 + θ := by linarith
  set t := (a + g) / (1 + θ) with ht
  have hst : a + g = (1 + θ) * t := by rw [ht]; field_simp
  rw [hst]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  rcases le_or_gt t 1 with h | h
  · rw [L_of_le t h]
    have : (1 + θ) * t ≤ 2 * t := by nlinarith
    have h2 : ((1 + θ) * t - 2 * w) * (1 - t) ≤ (2 * t - 2 * w) * (1 - t) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [sq_nonneg (1 + w - 2 * t)]
  · rw [L_of_ge t h.le]; nlinarith [sq_nonneg (1 - w)]

lemma np_lt (w p : ℝ) (hw1 : w < 1) (hne : p ≠ (1 + w) / 2) :
    2 * (p - w) * L p < (1 - w) ^ 2 / 2 := by
  rcases le_or_gt p 1 with h | h
  · rw [L_of_le p h]
    have : 0 < (1 + w - 2 * p) ^ 2 := by
      have : 1 + w - 2 * p ≠ 0 := by intro h'; apply hne; linarith
      positivity
    nlinarith
  · rw [L_of_ge p h.le]
    have : 0 < 1 - w := by linarith
    nlinarith

/-- Upper bound for BOGO policies, with the equality case for `w < θ`. -/
lemma bogo_le (θ w a g : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hg0 : 0 ≤ g) (hga : g ≤ a) :
    bogoProfit θ w a g ≤ V1 θ w ∧
      (w < θ → bogoProfit θ w a g = V1 θ w → a = (1 + w) / 2 ∧ g = (θ + w) / 2) := by
  have h1θ : 0 < 1 + θ := by linarith
  have ha0 : 0 ≤ a := le_trans hg0 hga
  rw [bogoProfit_eq θ w a g hθ0 ha0 hg0]
  rcases le_or_gt (θ * a) g with hA | hB
  · have hq : a ≤ g / θ := by rw [le_div_iff₀ hθ0]; linarith
    have ht : a ≤ (a + g) / (1 + θ) := by rw [le_div_iff₀ h1θ]; linarith
    rw [max_eq_right hq, max_eq_left ht, sub_self, mul_zero, add_zero]
    have h1 := np_le w a hw1
    have h2 := second_le θ w g hθ0 hg0
    have hsum : 2 * (a - w) * L a + (g - w) * L (g / θ) ≤ V1 θ w := by unfold V1; linarith
    refine ⟨by linarith, fun hw heq => ?_⟩
    have hw1' : w < 1 := lt_of_lt_of_le hw hθ1
    by_cases hga' : a = (1 + w) / 2
    · by_cases hgg : g = (θ + w) / 2
      · exact ⟨hga', hgg⟩
      · have := second_lt θ w g hθ0 hg0 hw hgg
        exfalso; unfold V1 at heq; linarith
    · have := np_lt w a hw1' hga'
      exfalso; unfold V1 at heq; linarith
  · have ha0' : 0 < a := by nlinarith
    have hq : g / θ ≤ a := by rw [div_le_iff₀ hθ0]; linarith
    have ht : (a + g) / (1 + θ) ≤ a := by rw [div_le_iff₀ h1θ]; linarith
    rw [max_eq_left hq, max_eq_right ht]
    rcases le_or_gt a 1 with ha1 | ha1
    · have hlt := caseB1_lt θ w a g hθ0 hθ1 hw0 hw1 hg0 hB ha1
      rw [L_of_le a ha1, L_of_le _ (le_trans ht ha1)]
      have e : (2 * a - 2 * w) * (1 - a) + (g - w) * (1 - a) +
          (a + g - 2 * w) * (1 - (a + g) / (1 + θ) - (1 - a)) =
          (1 - a) * (a - w) + (1 - (a + g) / (1 + θ)) * (a + g - 2 * w) := by ring
      rw [e]
      exact ⟨hlt.le, fun _ h => absurd h (ne_of_lt hlt)⟩
    · have hle := caseB2_le θ w a g hθ0 hθ1 hw0 hw1 hg0 ha1
      rw [L_of_ge a ha1.le]
      simp only [mul_zero, add_zero, zero_add, sub_zero]
      refine ⟨le_trans hle (V1_ge θ w hθ0), fun hw h => ?_⟩
      have := V1_gt θ w hθ0 hw
      exfalso; linarith

lemma policyB_le (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (π : BPolicy) (hπ : π.Feasible) :
    π.profit θ w ≤ V1 θ w ∧
      (w < θ → π.profit θ w = V1 θ w → π = .bogo ((1 + w) / 2) ((θ + w) / 2)) := by
  cases π with
  | single p =>
    simp only [BPolicy.Feasible] at hπ
    simp only [BPolicy.profit]
    rw [ind_int_np w p hπ]
    have h1 := np_le w p hw1
    refine ⟨le_trans h1 (V1_ge θ w hθ0), fun hw h => ?_⟩
    have := V1_gt θ w hθ0 hw
    exfalso; linarith
  | bogo a g =>
    simp only [BPolicy.Feasible] at hπ
    simp only [BPolicy.profit]
    obtain ⟨h1, h2⟩ := bogo_le θ w a g hθ0 hθ1 hw0 hw1 hπ.1 hπ.2
    refine ⟨h1, fun hw h => ?_⟩
    obtain ⟨e1, e2⟩ := h2 hw h
    rw [e1, e2]

lemma policyB_affine (θ w : ℝ) (hθ0 : 0 < θ) (π : BPolicy) (hπ : π.Feasible) :
    π.profit θ w = π.profit θ 0 - w * π.demand θ ∧ 0 ≤ π.demand θ := by
  cases π with
  | single p =>
    simp only [BPolicy.Feasible] at hπ
    simp only [BPolicy.profit, BPolicy.demand]
    rw [ind_int_np w p hπ, ind_int_np 0 p hπ, ind_int_npD p hπ]
    exact ⟨by ring, by have := L_nonneg p; linarith⟩
  | bogo a g =>
    simp only [BPolicy.Feasible] at hπ
    simp only [BPolicy.profit, BPolicy.demand]
    have ha0 : 0 ≤ a := le_trans hπ.1 hπ.2
    rw [bogoProfit_eq θ w a g hθ0 ha0 hπ.1, bogoProfit_eq θ 0 a g hθ0 ha0 hπ.1,
      bogoDemand_eq θ a g hθ0 ha0 hπ.1]
    refine ⟨by ring, ?_⟩
    have := L_nonneg a
    have := L_nonneg (max a (g / θ))
    have := L_anti (le_max_left ((a + g) / (1 + θ)) a)
    linarith

/-! ### Tangent (envelope) lemmas -/

lemma tan_left (R D w0 A B K δ : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ w, w0 - δ < w → w < w0 → R - w * D ≤ A + B * (w - w0) + K * (w - w0) ^ 2)
    (heq : R - w0 * D = A) : D ≤ -B := by
  by_contra hc
  push Not at hc
  set X := -D - B with hX
  have hX0 : 0 < -X := by linarith
  set ε := min (δ / 2) ((-X) / (K + 1)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hε1 : ε ≤ δ / 2 := min_le_left _ _
  have hε2 : ε ≤ (-X) / (K + 1) := min_le_right _ _
  have := h (w0 - ε) (by linarith) (by linarith)
  have h3 : -X * ε ≤ K * ε ^ 2 := by nlinarith
  have h4 : -X ≤ K * ε := by
    have := (mul_le_mul_iff_of_pos_right hε0).mp (by nlinarith : -X * ε ≤ (K * ε) * ε)
    linarith
  have h5 : K * ε ≤ K * ((-X) / (K + 1)) := mul_le_mul_of_nonneg_left hε2 hK
  have h6 : K * ((-X) / (K + 1)) < -X := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

lemma tan_right (R D w0 A B K δ : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ w, w0 < w → w < w0 + δ → R - w * D ≤ A + B * (w - w0) + K * (w - w0) ^ 2)
    (heq : R - w0 * D = A) : -B ≤ D := by
  by_contra hc
  push Not at hc
  set X := -D - B with hX
  have hX0 : 0 < X := by linarith
  set ε := min (δ / 2) (X / (K + 1)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hε1 : ε ≤ δ / 2 := min_le_left _ _
  have hε2 : ε ≤ X / (K + 1) := min_le_right _ _
  have := h (w0 + ε) (by linarith) (by linarith)
  have h4 : X ≤ K * ε := by
    have := (mul_le_mul_iff_of_pos_right hε0).mp (by nlinarith : X * ε ≤ (K * ε) * ε)
    linarith
  have h5 : K * ε ≤ K * (X / (K + 1)) := mul_le_mul_of_nonneg_left hε2 hK
  have h6 : K * (X / (K + 1)) < X := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-- If `R - wD ≤ V w` on `(0,1]` with equality at `w0`, and `V` has the quadratic upper
tangent `V w0 + B (w - w0) + K (w - w0)^2`, then `D = -B`. -/
lemma demand_eq_of_tangent (R D w0 B K : ℝ) (V : ℝ → ℝ) (hw0 : 0 < w0) (hw01 : w0 ≤ 1)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hB : w0 = 1 → B = 0)
    (hle : ∀ w, 0 < w → w ≤ 1 → R - w * D ≤ V w) (heq : R - w0 * D = V w0)
    (hV : ∀ w, 0 < w → w ≤ 1 → V w ≤ V w0 + B * (w - w0) + K * (w - w0) ^ 2) : D = -B := by
  have hL : D ≤ -B := by
    apply tan_left R D w0 (V w0) B K w0 hw0 hK _ heq
    intro w h1 h2
    exact le_trans (hle w (by linarith) (by linarith)) (hV w (by linarith) (by linarith))
  rcases lt_or_eq_of_le hw01 with h | h
  · have hR : -B ≤ D := by
      apply tan_right R D w0 (V w0) B K (1 - w0) (by linarith) hK _ heq
      intro w h1 h2
      exact le_trans (hle w (by linarith) (by linarith)) (hV w (by linarith) (by linarith))
    linarith
  · have := hB h; linarith

lemma V1_tangent (θ w0 w : ℝ) (hθ0 : 0 < θ) :
    V1 θ w ≤ V1 θ w0 + (-(1 - w0) - max (θ - w0) 0 / (2 * θ)) * (w - w0) +
      (1 / 2 + 1 / (4 * θ)) * (w - w0) ^ 2 := by
  unfold V1
  have key : (max (θ - w) 0) ^ 2 ≤ (max (θ - w0) 0) ^ 2 - 2 * max (θ - w0) 0 * (w - w0) +
      (w - w0) ^ 2 := by
    rcases le_total w θ with h1 | h1 <;> rcases le_total w0 θ with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; nlinarith
  have h4 : 0 < 4 * θ := by positivity
  have : (max (θ - w) 0) ^ 2 / (4 * θ) ≤
      ((max (θ - w0) 0) ^ 2 - 2 * max (θ - w0) 0 * (w - w0) + (w - w0) ^ 2) / (4 * θ) :=
    div_le_div_of_nonneg_right key h4.le
  have e : ((max (θ - w0) 0) ^ 2 - 2 * max (θ - w0) 0 * (w - w0) + (w - w0) ^ 2) / (4 * θ) =
      (max (θ - w0) 0) ^ 2 / (4 * θ) - max (θ - w0) 0 / (2 * θ) * (w - w0) +
        1 / (4 * θ) * (w - w0) ^ 2 := by
    field_simp; ring
  rw [e] at this
  nlinarith

/-- The optimal BOGO attains `V1` when `w ≤ θ`. -/
lemma bogo_opt_val (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hwθ : w ≤ θ) :
    bogoProfit θ w ((1 + w) / 2) ((θ + w) / 2) = V1 θ w := by
  have h1θ : 0 < 1 + θ := by linarith
  have hg0 : 0 ≤ (θ + w) / 2 := by linarith
  have ha0 : 0 ≤ (1 + w) / 2 := by linarith
  rw [bogoProfit_eq θ w _ _ hθ0 ha0 hg0]
  have hq : (1 + w) / 2 ≤ (θ + w) / 2 / θ := by
    rw [le_div_iff₀ hθ0]; nlinarith
  have ht : (1 + w) / 2 ≤ ((1 + w) / 2 + (θ + w) / 2) / (1 + θ) := by
    rw [le_div_iff₀ h1θ]; nlinarith
  rw [max_eq_right hq, max_eq_left ht, sub_self, mul_zero, add_zero,
    L_of_le _ (by linarith), L_of_le _ (by rw [div_le_one hθ0]; linarith)]
  unfold V1; rw [max_eq_left (by linarith)]
  field_simp; ring

/-- Profit of any best response equals `V1`. -/
lemma bestB_val (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (π : BPolicy) (hπ : IsBestRespB θ w π) : π.profit θ w = V1 θ w := by
  apply le_antisymm (policyB_le θ w hθ0 hθ1 hw0.le hw1 π hπ.1).1
  rcases le_or_gt w θ with h | h
  · have := hπ.2 (.bogo ((1 + w) / 2) ((θ + w) / 2)) ⟨by linarith, by linarith⟩
    simp only [BPolicy.profit] at this
    rw [bogo_opt_val θ w hθ0 hθ1 hw0.le h] at this; exact this
  · have := hπ.2 (.single ((1 + w) / 2)) (by simp only [BPolicy.Feasible]; linarith)
    have e2 : (BPolicy.single ((1 + w) / 2)).profit θ w = (1 - w) ^ 2 / 2 := by
      simp only [BPolicy.profit]
      rw [ind_int_np w _ (by linarith), L_of_le _ (by linarith)]; ring
    rw [e2] at this
    unfold V1; rw [max_eq_right (by linarith)]
    have : (0:ℝ) ^ 2 / (4 * θ) = 0 := by simp
    linarith

/-- Demand of any best response. -/
lemma bestB_demand (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (π : BPolicy) (hπ : IsBestRespB θ w π) :
    π.demand θ = 1 - w + max (θ - w) 0 / (2 * θ) := by
  obtain ⟨haff, hD⟩ := policyB_affine θ w hθ0 π hπ.1
  have hval := bestB_val θ w hθ0 hθ1 hw0 hw1 π hπ
  have := demand_eq_of_tangent (π.profit θ 0) (π.demand θ) w
    (-(1 - w) - max (θ - w) 0 / (2 * θ)) (1 / 2 + 1 / (4 * θ)) (V1 θ) hw0 hw1 (by positivity) hD
    (by intro h; rw [h]; rw [max_eq_right (by linarith)]; simp)
    (by
      intro w' h1 h2
      rw [← (policyB_affine θ w' hθ0 π hπ.1).1]
      exact (policyB_le θ w' hθ0 hθ1 h1.le h2 π hπ.1).1)
    (by rw [← haff]; exact hval)
    (fun w' _ _ => V1_tangent θ w w' hθ0)
  linarith


lemma bestB_exists (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    IsBestRespB θ w (if w ≤ θ then .bogo ((1 + w) / 2) ((θ + w) / 2) else .single ((1 + w) / 2)) := by
  split_ifs with h
  · have hval := bogo_opt_val θ w hθ0 hθ1 hw0.le h
    refine ⟨⟨by linarith, by linarith⟩, fun π' hπ' => ?_⟩
    simp only [BPolicy.profit]; rw [hval]
    exact (policyB_le θ w hθ0 hθ1 hw0.le hw1 π' hπ').1
  · push Not at h
    have hval : (BPolicy.single ((1 + w) / 2)).profit θ w = V1 θ w := by
      simp only [BPolicy.profit]
      rw [ind_int_np w _ (by linarith), L_of_le _ (by linarith)]
      unfold V1; rw [max_eq_right (by linarith)]; ring
    refine ⟨by simp only [BPolicy.Feasible]; linarith, fun π' hπ' => ?_⟩
    rw [hval]; exact (policyB_le θ w hθ0 hθ1 hw0.le hw1 π' hπ').1

/-! ### Price-reduction game -/

noncomputable def S0 (w : ℝ) : ℝ := (1 - w) ^ 2 / 4

noncomputable def Hp (θ w : ℝ) : ℝ := (max (2 * θ - (1 + θ) * w) 0) ^ 2 / (4 * θ * (1 + θ))

noncomputable def V3 (θ w : ℝ) : ℝ := S0 w + max (S0 w) (Hp θ w)

noncomputable def pdStar (θ w : ℝ) : ℝ := (2 * θ + (1 + θ) * w) / (2 * (1 + θ))

lemma S0_nonneg (w : ℝ) : 0 ≤ S0 w := by unfold S0; positivity

lemma Hp_nonneg (θ w : ℝ) (hθ0 : 0 < θ) : 0 ≤ Hp θ w := by
  unfold Hp; have : 0 < 1 + θ := by linarith
  positivity

/-- The pd-part of a PR policy's profit. -/
lemma h_le (θ w pd : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw1 : w ≤ 1) (hpd : 0 ≤ pd) :
    (pd - w) * L pd + (pd - w) * L (pd / θ) ≤ max (S0 w) (Hp θ w) ∧
      (S0 w < Hp θ w → pd ≠ pdStar θ w →
        (pd - w) * L pd + (pd - w) * L (pd / θ) < Hp θ w) := by
  have h1θ : 0 < 1 + θ := by linarith
  have hS := S0_nonneg w
  rcases le_or_gt pd θ with h | h
  · have hq : pd / θ ≤ 1 := by rw [div_le_one hθ0]; exact h
    rw [L_of_le pd (le_trans h hθ1), L_of_le _ hq]
    have e : (pd - w) * (1 - pd) + (pd - w) * (1 - pd / θ) =
        (pd - w) * (2 * θ - (1 + θ) * pd) / θ := by field_simp; ring
    rw [e]
    have hY : 0 ≤ 2 * θ - (1 + θ) * pd := by nlinarith
    rcases le_or_gt pd w with hpw | hpw
    · have : (pd - w) * (2 * θ - (1 + θ) * pd) / θ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hY) hθ0.le
      refine ⟨le_trans this (le_trans hS (le_max_left _ _)), fun hlt _ => by linarith⟩
    · have hpos : 0 < 2 * θ - (1 + θ) * w := by nlinarith
      have hHp : Hp θ w = (2 * θ - (1 + θ) * w) ^ 2 / (4 * θ * (1 + θ)) := by
        unfold Hp; rw [max_eq_left hpos.le]
      have key : Hp θ w - (pd - w) * (2 * θ - (1 + θ) * pd) / θ =
          (2 * θ + (1 + θ) * w - 2 * (1 + θ) * pd) ^ 2 / (4 * θ * (1 + θ)) := by
        rw [hHp]; field_simp; ring
      have hnn : 0 ≤ (2 * θ + (1 + θ) * w - 2 * (1 + θ) * pd) ^ 2 / (4 * θ * (1 + θ)) := by
        positivity
      refine ⟨by linarith [le_max_right (S0 w) (Hp θ w)], fun _ hne => ?_⟩
      have : 0 < (2 * θ + (1 + θ) * w - 2 * (1 + θ) * pd) ^ 2 / (4 * θ * (1 + θ)) := by
        have : 2 * θ + (1 + θ) * w - 2 * (1 + θ) * pd ≠ 0 := by
          intro h0; apply hne; unfold pdStar; field_simp; linarith
        positivity
      linarith
  · have hq : 1 ≤ pd / θ := by rw [le_div_iff₀ hθ0]; linarith
    rw [L_of_ge _ hq, mul_zero, add_zero]
    have := half_le w pd hw1
    refine ⟨le_trans this (le_max_left _ _), fun hlt _ => ?_⟩
    unfold S0 at hlt; linarith

lemma half_lt (w p : ℝ) (hw1 : w < 1) (hne : p ≠ (1 + w) / 2) : (p - w) * L p < (1 - w) ^ 2 / 4 := by
  have := np_lt w p hw1 hne; nlinarith

lemma policyP_le (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw1 : w ≤ 1)
    (π : PPolicy) (hπ : π.Feasible) :
    π.profit θ w ≤ V3 θ w ∧
      (S0 w < Hp θ w → w < 1 → π.profit θ w = V3 θ w →
        π = .priceRed ((1 + w) / 2) (pdStar θ w)) := by
  have hS := S0_nonneg w
  cases π with
  | single p =>
    simp only [PPolicy.Feasible] at hπ
    simp only [PPolicy.profit]
    rw [ind_int_np w p hπ]
    have h1 := np_le w p hw1
    have h2 : 2 * (p - w) * L p ≤ 2 * S0 w := by unfold S0; linarith
    refine ⟨by unfold V3; linarith [le_max_left (S0 w) (Hp θ w)], fun hlt _ heq => ?_⟩
    unfold V3 at heq; rw [max_eq_right hlt.le] at heq
    exfalso; linarith
  | priceRed pr pd =>
    simp only [PPolicy.Feasible] at hπ
    simp only [PPolicy.profit]
    rw [prProfit_eq θ w pr pd hθ0 hθ1 hπ.1 hπ.2]
    obtain ⟨hh1, hh2⟩ := h_le θ w pd hθ0 hθ1 hw1 hπ.1
    have hr := half_le w pr hw1
    refine ⟨by unfold V3 S0 at *; linarith, fun hlt hw heq => ?_⟩
    unfold V3 at heq; rw [max_eq_right hlt.le] at heq
    rw [max_eq_right hlt.le] at hh1
    by_cases hpr : pr = (1 + w) / 2
    · by_cases hpd : pd = pdStar θ w
      · rw [hpr, hpd]
      · have := hh2 hlt hpd; exfalso; unfold S0 at *; linarith
    · have := half_lt w pr hw hpr; exfalso; unfold S0 at *; linarith

lemma policyP_affine (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (π : PPolicy) (hπ : π.Feasible) :
    π.profit θ w = π.profit θ 0 - w * π.demand θ ∧ 0 ≤ π.demand θ := by
  cases π with
  | single p =>
    simp only [PPolicy.Feasible] at hπ
    simp only [PPolicy.profit, PPolicy.demand]
    rw [ind_int_np w p hπ, ind_int_np 0 p hπ, ind_int_npD p hπ]
    exact ⟨by ring, by have := L_nonneg p; linarith⟩
  | priceRed pr pd =>
    simp only [PPolicy.Feasible] at hπ
    simp only [PPolicy.profit, PPolicy.demand]
    rw [prProfit_eq θ w pr pd hθ0 hθ1 hπ.1 hπ.2, prProfit_eq θ 0 pr pd hθ0 hθ1 hπ.1 hπ.2,
      prDemand_eq θ pr pd hθ0 hθ1 hπ.1 hπ.2]
    refine ⟨by ring, ?_⟩
    have := L_nonneg pr; have := L_nonneg pd; have := L_nonneg (pd / θ)
    linarith

/-- Facts about `θ̄`. -/
lemma tb_facts (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    thetaBar θ ≤ θ ∧ (1 + θ) * thetaBar θ ≤ 2 * θ ^ 2 ∧ (θ ≤ 1 / 3 → thetaBar θ ≤ 0) ∧
    ∀ w, 0 ≤ w → w ≤ 1 →
      (w ≤ thetaBar θ → S0 w ≤ Hp θ w ∧ (1 + θ) * w ≤ 2 * θ) ∧
      (w < thetaBar θ → S0 w < Hp θ w) ∧
      (thetaBar θ ≤ w → Hp θ w ≤ S0 w) := by
  have h1θ : 0 < 1 + θ := by linarith
  set q := Real.sqrt (θ / (1 + θ)) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = θ / (1 + θ) := Real.sq_sqrt (by positivity)
  have hq2' : (1 + θ) * q ^ 2 = θ := by rw [hq2]; field_simp
  have hq1 : q < 1 := by
    have : q ^ 2 < 1 := by rw [hq2, div_lt_one h1θ]; linarith
    nlinarith
  have htb : thetaBar θ = θ - (1 - θ) * q := rfl
  have hΔ : ∀ w, 2 * θ - (1 + θ) * w - (1 + θ) * q * (1 - w) =
      (1 + θ) * (1 - q) * (thetaBar θ - w) := by
    intro w; rw [htb]; linear_combination (-(1 - θ)) * hq2'
  have hpos1 : 0 < (1 + θ) * (1 - q) := by nlinarith
  have hS0eq : ∀ w, S0 w = ((1 + θ) * q * (1 - w)) ^ 2 / (4 * θ * (1 + θ)) := by
    intro w; unfold S0
    have : ((1 + θ) * q * (1 - w)) ^ 2 = θ * (1 + θ) * (1 - w) ^ 2 := by
      have : ((1 + θ) * q * (1 - w)) ^ 2 = (1 + θ) * ((1 + θ) * q ^ 2) * (1 - w) ^ 2 := by ring
      rw [this, hq2']; ring
    rw [this]; field_simp
  refine ⟨by rw [htb]; nlinarith, by rw [htb]; nlinarith, fun h => by rw [htb]; nlinarith, ?_⟩
  intro w hw0 hw1
  have hA : 0 ≤ (1 + θ) * q * (1 - w) := by
    apply mul_nonneg (mul_nonneg h1θ.le hq0) (by linarith)
  have hD : 0 < 4 * θ * (1 + θ) := by positivity
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 : (1 + θ) * q * (1 - w) ≤ 2 * θ - (1 + θ) * w := by
      have := hΔ w; nlinarith
    refine ⟨?_, by linarith⟩
    rw [hS0eq w]; unfold Hp; rw [max_eq_left (by linarith)]
    apply div_le_div_of_nonneg_right _ hD.le
    exact pow_le_pow_left₀ hA h1 2
  · have h1 : (1 + θ) * q * (1 - w) < 2 * θ - (1 + θ) * w := by
      have := hΔ w; nlinarith
    rw [hS0eq w]; unfold Hp; rw [max_eq_left (by linarith)]
    apply div_lt_div_of_pos_right _ hD
    exact pow_lt_pow_left₀ h1 hA (by norm_num)
  · have h1 : 2 * θ - (1 + θ) * w ≤ (1 + θ) * q * (1 - w) := by
      have := hΔ w; nlinarith
    rw [hS0eq w]; unfold Hp
    rcases le_or_gt (2 * θ - (1 + θ) * w) 0 with h2 | h2
    · rw [max_eq_right h2]; simp; positivity
    · rw [max_eq_left h2.le]
      apply div_le_div_of_nonneg_right _ hD.le
      exact pow_le_pow_left₀ h2.le h1 2

lemma PR_opt_val (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (h2 : (1 + θ) * w ≤ 2 * θ) (h3 : (1 + θ) * w ≤ 2 * θ ^ 2) :
    prProfit θ w ((1 + w) / 2) (pdStar θ w) = S0 w + Hp θ w ∧
      prDemand θ ((1 + w) / 2) (pdStar θ w) = (3 * θ - w * (1 + 2 * θ)) / (2 * θ) := by
  have h1θ : 0 < 1 + θ := by linarith
  have hpd0 : 0 ≤ pdStar θ w := by unfold pdStar; positivity
  have hpdr : pdStar θ w ≤ (1 + w) / 2 := by
    unfold pdStar; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hpdθ : pdStar θ w ≤ θ := by
    unfold pdStar; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hq : pdStar θ w / θ ≤ 1 := by rw [div_le_one hθ0]; exact hpdθ
  rw [prProfit_eq θ w _ _ hθ0 hθ1 hpd0 hpdr, prDemand_eq θ _ _ hθ0 hθ1 hpd0 hpdr,
    L_of_le _ (le_trans hpdθ hθ1), L_of_le _ (by linarith), L_of_le _ hq]
  unfold S0 Hp pdStar; rw [max_eq_left (by linarith)]
  constructor <;> field_simp <;> ring


lemma single_val (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    npProfit w ((1 + w) / 2) = (1 - w) ^ 2 / 2 := by
  rw [ind_int_np w _ (by linarith), L_of_le _ (by linarith)]; ring

/-- PR game, region where the price reduction is optimal. -/
lemma bestP_a (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hwt : w ≤ thetaBar θ) :
    IsBestRespP θ w (.priceRed ((1 + w) / 2) (pdStar θ w)) ∧
      prProfit θ w ((1 + w) / 2) (pdStar θ w) = V3 θ w ∧ V3 θ w = S0 w + Hp θ w ∧
      prDemand θ ((1 + w) / 2) (pdStar θ w) = (3 * θ - w * (1 + 2 * θ)) / (2 * θ) := by
  obtain ⟨htθ, ht2, -, hw⟩ := tb_facts θ hθ0 hθ1
  have hw1 : w ≤ 1 := by linarith
  obtain ⟨hSH, h2⟩ := (hw w hw0.le hw1).1 hwt
  have h3 : (1 + θ) * w ≤ 2 * θ ^ 2 := by nlinarith
  obtain ⟨hv, hd⟩ := PR_opt_val θ w hθ0 hθ1 hw0.le hw1 h2 h3
  have hV : V3 θ w = S0 w + Hp θ w := by unfold V3; rw [max_eq_right hSH]
  have hpd0 : 0 ≤ pdStar θ w := by unfold pdStar; positivity
  have hpdr : pdStar θ w ≤ (1 + w) / 2 := by
    unfold pdStar; rw [div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨⟨⟨hpd0, hpdr⟩, fun π' hπ' => ?_⟩, by rw [hv, hV], hV, hd⟩
  simp only [PPolicy.profit]; rw [hv, ← hV]
  exact (policyP_le θ w hθ0 hθ1 hw1 π' hπ').1

/-- PR game, region where no promotion is optimal. -/
lemma bestP_b (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (htw : thetaBar θ ≤ w) :
    IsBestRespP θ w (.single ((1 + w) / 2)) ∧ V3 θ w = (1 - w) ^ 2 / 2 := by
  obtain ⟨-, -, -, hw⟩ := tb_facts θ hθ0 hθ1
  have hHS := (hw w hw0.le hw1).2.2 htw
  have hV : V3 θ w = (1 - w) ^ 2 / 2 := by unfold V3; rw [max_eq_left hHS]; unfold S0; ring
  refine ⟨⟨by simp only [PPolicy.Feasible]; linarith, fun π' hπ' => ?_⟩, hV⟩
  simp only [PPolicy.profit]; rw [single_val w hw0 hw1, ← hV]
  exact (policyP_le θ w hθ0 hθ1 hw1 π' hπ').1

lemma bestP_val (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (π : PPolicy) (hπ : IsBestRespP θ w π) : π.profit θ w = V3 θ w := by
  apply le_antisymm (policyP_le θ w hθ0 hθ1 hw1 π hπ.1).1
  rcases le_or_gt w (thetaBar θ) with h | h
  · obtain ⟨_, hv, -⟩ := bestP_a θ w hθ0 hθ1 hw0 h
    have := hπ.2 _ (bestP_a θ w hθ0 hθ1 hw0 h).1.1
    simp only [PPolicy.profit] at this; rw [hv] at this; exact this
  · obtain ⟨hb, hV⟩ := bestP_b θ w hθ0 hθ1 hw0 hw1 h.le
    have := hπ.2 _ hb.1
    have e : (PPolicy.single ((1 + w) / 2)).profit θ w = (1 - w) ^ 2 / 2 := by
      simp only [PPolicy.profit]; exact single_val w hw0 hw1
    rw [e] at this; rw [hV]; exact this

/-- Demand of PR best responses where no promotion is optimal (strictly above `θ̄`). -/
lemma bestP_demand_b (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (htw : thetaBar θ < w) (π : PPolicy) (hπ : IsBestRespP θ w π) : π.demand θ = 1 - w := by
  obtain ⟨haff, hD⟩ := policyP_affine θ w hθ0 hθ1 π hπ.1
  have hval := bestP_val θ w hθ0 hθ1 hw0 hw1 π hπ
  have hV := (bestP_b θ w hθ0 hθ1 hw0 hw1 htw.le).2
  have heq : π.profit θ 0 - w * π.demand θ = (1 - w) ^ 2 / 2 := by rw [← haff, hval, hV]
  have hbound : ∀ w', 0 < w' → w' ≤ 1 → thetaBar θ ≤ w' →
      π.profit θ 0 - w' * π.demand θ ≤
        (1 - w) ^ 2 / 2 + (-(1 - w)) * (w' - w) + (1 / 2) * (w' - w) ^ 2 := by
    intro w' h1 h2 h3
    rw [← (policyP_affine θ w' hθ0 hθ1 π hπ.1).1]
    have := (policyP_le θ w' hθ0 hθ1 h2 π hπ.1).1
    rw [(bestP_b θ w' hθ0 hθ1 h1 h2 h3).2] at this
    nlinarith
  set m := max (thetaBar θ) 0 with hm
  have hmw : m < w := max_lt htw hw0
  have hL : π.demand θ ≤ -(-(1 - w)) := by
    apply tan_left _ _ w _ _ (1 / 2) (w - m) (by linarith) (by norm_num) _ heq
    intro w' h1 h2
    exact hbound w' (by linarith [le_max_right (thetaBar θ) 0]) (by linarith)
      (by linarith [le_max_left (thetaBar θ) 0])
  rcases lt_or_eq_of_le hw1 with h | h
  · have hR : -(-(1 - w)) ≤ π.demand θ := by
      apply tan_right _ _ w _ _ (1 / 2) (1 - w) (by linarith) (by norm_num) _ heq
      intro w' h1 h2
      exact hbound w' (by linarith) (by linarith) (by linarith)
    linarith
  · rw [h] at hL ⊢; linarith


/-- `c < c̃(θ)` gives `c(1+2θ) < θ(4θ-1)` and `(3θ - c(1+2θ))^2 > 2θ(1+2θ)(1-c)^2`. -/
lemma cTilde_facts (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cTilde θ) :
    c * (1 + 2 * θ) < θ * (4 * θ - 1) ∧ c < 1 ∧
      2 * θ * (1 + 2 * θ) * (1 - c) ^ 2 < (3 * θ - c * (1 + 2 * θ)) ^ 2 := by
  unfold cTilde at hc
  have hs : 0 < 1 + 2 * θ := by linarith
  set r := Real.sqrt (2 * θ / (1 + 2 * θ)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * θ / (1 + 2 * θ) := Real.sq_sqrt (by positivity)
  have hr2' : r ^ 2 * (1 + 2 * θ) = 2 * θ := by rw [hr2]; field_simp
  have hr1 : r < 1 := by nlinarith
  have hc1 : c < 1 := by nlinarith
  have hθr : (1 - θ) * r * (1 - r) ≥ 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) hr0) (by linarith)
  refine ⟨?_, hc1, ?_⟩
  · -- θ(4θ-1)/s - c̃ = (1-θ) r (1-r)
    have : c * (1 + 2 * θ) < (θ - (1 - θ) * r) * (1 + 2 * θ) := by nlinarith
    nlinarith
  · have hid : (θ - (1 - θ) * r) * ((1 + 2 * θ) * (1 - r)) = 3 * θ - (1 + 2 * θ) * r := by
      nlinarith
    have hpos : 0 < (1 + 2 * θ) * (1 - r) := by nlinarith
    have h1 : c * ((1 + 2 * θ) * (1 - r)) < 3 * θ - (1 + 2 * θ) * r := by
      rw [← hid]; exact mul_lt_mul_of_pos_right hc hpos
    -- 3θ - cs > s r (1 - c) ≥ 0
    have h2 : (1 + 2 * θ) * r * (1 - c) < 3 * θ - c * (1 + 2 * θ) := by nlinarith
    have h3 : 0 ≤ (1 + 2 * θ) * r * (1 - c) := by
      apply mul_nonneg (mul_nonneg hs.le hr0) (by linarith)
    have h4 : ((1 + 2 * θ) * r * (1 - c)) ^ 2 < (3 * θ - c * (1 + 2 * θ)) ^ 2 := by
      apply pow_lt_pow_left₀ h2 h3 (by norm_num)
    have h5 : ((1 + 2 * θ) * r * (1 - c)) ^ 2 = 2 * θ * (1 + 2 * θ) * (1 - c) ^ 2 := by
      have : ((1 + 2 * θ) * r * (1 - c)) ^ 2 = (1 + 2 * θ) * (r ^ 2 * (1 + 2 * θ)) * (1 - c) ^ 2 := by
        ring
      rw [this, hr2']; ring
    linarith

/-- Manufacturer's profit against best responses in the BOGO game. -/
noncomputable def FB (θ c w : ℝ) : ℝ := (w - c) * (1 - w + max (θ - w) 0 / (2 * θ))

lemma FB_le (θ c w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cTilde θ)
    (hw0 : 0 < w) (hw1 : w ≤ 1) :
    FB θ c w ≤ (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) ∧
      (FB θ c w = (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) →
        w = (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ))) := by
  obtain ⟨hreg, hc1, hgap⟩ := cTilde_facts θ c hθ0 hθ1 hc0 hc
  have hs : 0 < 1 + 2 * θ := by linarith
  unfold FB
  rcases le_or_gt w θ with h | h
  · rw [max_eq_left (by linarith)]
    have e : (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) -
        (w - c) * (1 - w + (θ - w) / (2 * θ)) =
        (1 + 2 * θ) * (w - (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ))) ^ 2 / (2 * θ) := by
      field_simp; ring
    have hnn : 0 ≤ (1 + 2 * θ) * (w - (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ))) ^ 2 /
        (2 * θ) := by positivity
    refine ⟨by linarith, fun heq => ?_⟩
    have h0 : (1 + 2 * θ) * (w - (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ))) ^ 2 / (2 * θ) = 0 :=
      by linarith
    have : (w - (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ))) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h0 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · linarith
        · exact h''
      · linarith
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · rw [max_eq_right (by linarith)]
    have hM : (1 - c) ^ 2 / 4 < (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      have : 3 * θ - c - 2 * c * θ = 3 * θ - c * (1 + 2 * θ) := by ring
      rw [this]; nlinarith
    have : (w - c) * (1 - w + 0 / (2 * θ)) ≤ (1 - c) ^ 2 / 4 := by
      simp; nlinarith [sq_nonneg (1 + c - 2 * w)]
    exact ⟨by linarith, fun heq => by linarith⟩

/-- In the region `0 ≤ c < c̄(θ)`: `c (1 + 2θ) < θ (4θ − 1)` and `θ > 1/2`. -/
lemma region (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cBar θ) :
    c * (1 + 2 * θ) < θ * (4 * θ - 1) ∧ 1 / 2 < θ := by
  unfold cBar at hc
  have hs : 0 < 1 + 2 * θ := by linarith
  have hq0 : 0 ≤ θ / (1 + θ) := by positivity
  have hq1 : θ / (1 + θ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hsq : θ / (1 + θ) ≤ Real.sqrt (θ / (1 + θ)) := by
    rw [Real.le_sqrt hq0 hq0]; nlinarith
  have hsq0 : 0 ≤ Real.sqrt (θ / (1 + θ)) := Real.sqrt_nonneg _
  have h1 : c < θ * (4 * θ - 1) / (1 + 2 * θ) := by nlinarith
  refine ⟨by rwa [lt_div_iff₀ hs] at h1, ?_⟩
  by_contra hθ
  push Not at hθ
  have h2 : c < θ * (4 * θ - 1) / (1 + 2 * θ) - 2 * (1 - θ) * (θ / (1 + θ)) := by nlinarith
  have h3 : θ * (4 * θ - 1) / (1 + 2 * θ) - 2 * (1 - θ) * (θ / (1 + θ)) =
      θ * (8 * θ ^ 2 + θ - 3) / ((1 + 2 * θ) * (1 + θ)) := by
    field_simp; ring
  rw [h3] at h2
  have h4 : θ * (8 * θ ^ 2 + θ - 3) / ((1 + 2 * θ) * (1 + θ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · positivity
  linarith


end BOGOPromo.NoStockpile.Aux

namespace BOGOPromo.NoStockpile.Aux

open BOGOPromo.NoStockpile

lemma V3_le_V1 (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    V3 θ w ≤ V1 θ w ∧ (w ≤ thetaBar θ → V1 θ w - V3 θ w = (1 - θ) ^ 2 / (4 * (1 + θ))) := by
  have h1θ : 0 < 1 + θ := by linarith
  obtain ⟨htθ, -, -, hwf⟩ := tb_facts θ hθ0 hθ1
  have key : w ≤ thetaBar θ → V1 θ w - V3 θ w = (1 - θ) ^ 2 / (4 * (1 + θ)) := by
    intro h
    obtain ⟨hSH, h2⟩ := (hwf w hw0 hw1).1 h
    unfold V1 V3; rw [max_eq_right hSH]; unfold S0 Hp
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp; ring
  refine ⟨?_, key⟩
  rcases le_or_gt w (thetaBar θ) with h | h
  · have := key h
    have : 0 ≤ (1 - θ) ^ 2 / (4 * (1 + θ)) := by positivity
    linarith
  · have hHS := (hwf w hw0 hw1).2.2 h.le
    unfold V3; rw [max_eq_left hHS]
    have := V1_ge θ w hθ0; unfold S0; linarith

lemma mono_adv' (θ₁ θ₂ : ℝ) (h1 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ 1) :
    (1 - θ₂) ^ 2 / (4 * (1 + θ₂)) < (1 - θ₁) ^ 2 / (4 * (1 + θ₁)) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have ha : (1 - θ₂) ^ 2 < (1 - θ₁) ^ 2 := by nlinarith
  have hb : 0 ≤ (1 - θ₂) ^ 2 := sq_nonneg _
  nlinarith

end BOGOPromo.NoStockpile.Aux

open BOGOPromo.NoStockpile BOGOPromo.NoStockpile.Aux

theorem solution :
    (∀ θ w : ℝ, 0 < θ → θ ≤ 1 → 0 < w → w ≤ 1 →
      ∀ πd : PPolicy, ∀ πb : BPolicy, IsBestRespP θ w πd → IsBestRespB θ w πb →
        πd.profit θ w ≤ πb.profit θ w) ∧
    (∀ θ₁ θ₂ w : ℝ, 1 / 3 < θ₁ → θ₁ < θ₂ → θ₂ ≤ 1 → 0 < w → w ≤ thetaBar θ₁ → w ≤ thetaBar θ₂ →
      ∀ (πb₁ πb₂ : BPolicy) (πd₁ πd₂ : PPolicy),
        IsBestRespB θ₁ w πb₁ → IsBestRespP θ₁ w πd₁ →
        IsBestRespB θ₂ w πb₂ → IsBestRespP θ₂ w πd₂ →
        πb₂.profit θ₂ w - πd₂.profit θ₂ w < πb₁.profit θ₁ w - πd₁.profit θ₁ w) := by
  constructor
  · intro θ w hθ0 hθ1 hw0 hw1 πd πb hd hb
    rw [bestP_val θ w hθ0 hθ1 hw0 hw1 πd hd, bestB_val θ w hθ0 hθ1 hw0 hw1 πb hb]
    exact (V3_le_V1 θ w hθ0 hθ1 hw0.le hw1).1
  · intro θ₁ θ₂ w h1 h12 h2 hw0 hwt1 hwt2 πb₁ πb₂ πd₁ πd₂ hb1 hd1 hb2 hd2
    have h1' : 0 < θ₁ := by linarith
    have h2' : 0 < θ₂ := by linarith
    have hθ11 : θ₁ ≤ 1 := by linarith
    have hw1 : w ≤ 1 := by linarith [(tb_facts θ₂ h2' h2).1]
    rw [bestP_val θ₁ w h1' hθ11 hw0 hw1 πd₁ hd1, bestB_val θ₁ w h1' hθ11 hw0 hw1 πb₁ hb1,
      bestP_val θ₂ w h2' h2 hw0 hw1 πd₂ hd2, bestB_val θ₂ w h2' h2 hw0 hw1 πb₂ hb2,
      (V3_le_V1 θ₁ w h1' hθ11 hw0.le hw1).2 hwt1, (V3_le_V1 θ₂ w h2' h2 hw0.le hw1).2 hwt2]
    exact mono_adv' θ₁ θ₂ h1' h12 h2
