-- Prove2me | solution 1 for BertsekasShreve.FiniteHorizon.multiplicative_F1_F2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:34:29.405788+00:00
-- url     : https://prove2.me/submissions/d0cb7ba1-c76a-44da-9135-d86380ab706a

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels



namespace BertsekasShreve.FiniteHorizon

open Model Filter Topology

namespace MulAux

open MeasureTheory

theorem tsum_iInf_anti {W : Type*} [Countable W] (a : ℕ → W → ENNReal)
    (ha : ∀ n w, a (n + 1) w ≤ a n w) (hfin : ∑' w, a 0 w ≠ ⊤) :
    ∑' w, ⨅ n, a n w = ⨅ n, ∑' w, a n w := by
  letI : MeasurableSpace W := ⊤
  have hm : ∀ n, Measurable (a n) := fun n => measurable_from_top
  have hanti : Antitone a := antitone_nat_of_succ_le fun n w => ha n w
  calc ∑' w, ⨅ n, a n w = ∫⁻ w, ⨅ n, a n w ∂Measure.count :=
        (lintegral_count' measurable_from_top).symm
    _ = ⨅ n, ∫⁻ w, a n w ∂Measure.count :=
        lintegral_iInf hm hanti (by rwa [lintegral_count' (hm 0)])
    _ = _ := by congr 1; funext n; exact lintegral_count' (hm n)

theorem tsum_iSup_mono {W : Type*} [Countable W] (a : ℕ → W → ENNReal)
    (ha : ∀ n w, a n w ≤ a (n + 1) w) :
    ∑' w, ⨆ n, a n w = ⨆ n, ∑' w, a n w := by
  letI : MeasurableSpace W := ⊤
  have hm : ∀ n, Measurable (a n) := fun n => measurable_from_top
  have hmono : Monotone a := monotone_nat_of_le_succ fun n w => ha n w
  rw [← lintegral_count' (measurable_from_top)]
  rw [lintegral_iSup hm hmono]
  congr 1; funext n
  exact lintegral_count' (hm n)

theorem expect_of_ne_top {W : Type*} (p : PMF W) (z : W → EReal)
    (h : ∑' w, p w * (z w).toENNReal ≠ ⊤) :
    expect p z = ((∑' w, p w * (z w).toENNReal : ENNReal) : EReal) -
      ((∑' w, p w * (-(z w)).toENNReal : ENNReal) : EReal) := by
  simp only [expect, if_neg h]

theorem P_ne_top_of_lt {W : Type*} (p : PMF W) (z : W → EReal) (h : expect p z < ⊤) :
    ∑' w, p w * (z w).toENNReal ≠ ⊤ := by
  intro hP
  simp only [expect, if_pos hP] at h
  exact lt_irrefl _ h

/-- pointwise convergence of `g * y k` -/
theorem tendsto_mul_seq (gw : EReal) (hg : 0 ≤ gw) (y : ℕ → EReal) (yl : EReal)
    (hanti : ∀ k, y (k + 1) ≤ y k) (hy : Tendsto y atTop (𝓝 yl))
    (h0 : gw * y 0 ≠ ⊤) : Tendsto (fun k => gw * y k) atTop (𝓝 (gw * yl)) := by
  have hA : Antitone y := antitone_nat_of_succ_le hanti
  have hyl : ∀ k, yl ≤ y k := fun k => hA.le_of_tendsto hy k
  rcases eq_or_ne gw 0 with h | h
  · subst h; simp only [zero_mul]; exact tendsto_const_nhds
  rcases eq_or_ne gw ⊤ with ht | ht
  · subst ht
    have hy0 : y 0 ≤ 0 := by
      by_contra hc; push_neg at hc
      exact h0 (EReal.top_mul_of_pos hc)
    rcases lt_or_eq_of_le ((hyl 0).trans hy0) with hneg | hzero
    · have hev : ∀ᶠ k in atTop, y k < 0 := hy.eventually (gt_mem_nhds hneg)
      rw [EReal.top_mul_of_neg hneg]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with k hk
      rw [EReal.top_mul_of_neg hk]
    · have : ∀ k, y k = 0 := fun k =>
        le_antisymm ((hA (Nat.zero_le k)).trans hy0) (hzero ▸ hyl k)
      simp only [this, ← hzero]
      exact tendsto_const_nhds
  · have hb : gw ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hg
    have hc := EReal.continuousAt_mul (p := (gw, yl)) (Or.inl h) (Or.inl h) (Or.inl hb) (Or.inl ht)
    exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds hy)

theorem F1_core {S C W : Type*} [Countable W] (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) : m.AssumptionF1 := by
  intro J hJ hfin Jlim hlim x u hu
  have hA : ∀ y, Antitone (fun k => J k y) := fun y => antitone_nat_of_succ_le fun k => hJ k y
  have hJl : ∀ k y, Jlim y ≤ J k y := fun k y => (hA y).le_of_tendsto (hlim y) k
  rw [hH]
  simp only [multiplicativeH]
  set q := p x u
  set z : ℕ → W → EReal := fun k w => g x u w * J k (f x u w) with hz
  set zl : W → EReal := fun w => g x u w * Jlim (f x u w) with hzl
  have hz_anti : ∀ k w, z (k + 1) w ≤ z k w := fun k w =>
    mul_le_mul_of_nonneg_left (hJ k _) (hg x u hu w)
  have hzl_le : ∀ k w, zl w ≤ z k w := fun k w =>
    mul_le_mul_of_nonneg_left (hJl k _) (hg x u hu w)
  have hP0 : ∑' w, q w * (z 0 w).toENNReal ≠ ⊤ := by
    have := hfin x u hu
    rw [hH] at this
    exact P_ne_top_of_lt q _ this
  -- pointwise convergence
  have hpt : ∀ w, q w ≠ 0 → Tendsto (fun k => z k w) atTop (𝓝 (zl w)) := by
    intro w hw
    apply tendsto_mul_seq _ (hg x u hu w) _ _ (fun k => hJ k _) (hlim _)
    intro htop
    apply hP0
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    refine le_trans ?_ (ENNReal.le_tsum w)
    show (r : ENNReal) ≤ q w * (z 0 w).toENNReal
    rw [show z 0 w = ⊤ from htop, EReal.toENNReal_top, ENNReal.mul_top hw]
    exact le_top
  set a : ℕ → W → ENNReal := fun k w => q w * (z k w).toENNReal with ha
  set b : ℕ → W → ENNReal := fun k w => q w * (-(z k w)).toENNReal with hb
  have ha_anti : ∀ k w, a (k + 1) w ≤ a k w := fun k w => by
    simp only [ha]; gcongr; exact EReal.toENNReal_le_toENNReal (hz_anti k w)
  have hb_mono : ∀ k w, b k w ≤ b (k + 1) w := fun k w => by
    simp only [hb]; gcongr; exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hz_anti k w))
  set al : W → ENNReal := fun w => q w * (zl w).toENNReal with hal
  set bl : W → ENNReal := fun w => q w * (-(zl w)).toENNReal with hbl
  have hpa : ∀ w, Tendsto (fun k => a k w) atTop (𝓝 (al w)) ∧
      Tendsto (fun k => b k w) atTop (𝓝 (bl w)) := by
    intro w
    rcases eq_or_ne (q w) 0 with h0 | h0
    · simp only [ha, hb, hal, hbl, h0, zero_mul]; exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
    · have hzt := hpt w h0
      have hne : q w ≠ ⊤ := PMF.apply_ne_top q w
      exact ⟨ENNReal.Tendsto.const_mul (EReal.continuous_toENNReal.tendsto _ |>.comp hzt) (Or.inr hne),
        ENNReal.Tendsto.const_mul
          (EReal.continuous_toENNReal.tendsto _ |>.comp (continuous_neg.tendsto _ |>.comp hzt))
          (Or.inr hne)⟩
  have hal_eq : al = fun w => ⨅ k, a k w := by
    funext w
    exact tendsto_nhds_unique (hpa w).1
      (tendsto_atTop_iInf (antitone_nat_of_succ_le fun k => ha_anti k w))
  have hbl_eq : bl = fun w => ⨆ k, b k w := by
    funext w
    exact tendsto_nhds_unique (hpa w).2
      (tendsto_atTop_iSup (monotone_nat_of_le_succ fun k => hb_mono k w))
  have hPanti : Antitone (fun k => ∑' w, a k w) :=
    antitone_nat_of_succ_le fun k => ENNReal.tsum_le_tsum fun w => ha_anti k w
  have hQmono : Monotone (fun k => ∑' w, b k w) :=
    monotone_nat_of_le_succ fun k => ENNReal.tsum_le_tsum fun w => hb_mono k w
  have hPlim : Tendsto (fun k => ∑' w, a k w) atTop (𝓝 (∑' w, al w)) := by
    rw [hal_eq, tsum_iInf_anti a ha_anti hP0]
    exact tendsto_atTop_iInf hPanti
  have hQlim : Tendsto (fun k => ∑' w, b k w) atTop (𝓝 (∑' w, bl w)) := by
    rw [hbl_eq, tsum_iSup_mono b hb_mono]
    exact tendsto_atTop_iSup hQmono
  have hPk : ∀ k, ∑' w, a k w ≠ ⊤ := fun k => ne_top_of_le_ne_top hP0 (hPanti (Nat.zero_le k))
  have hPl : ∑' w, al w ≠ ⊤ :=
    ne_top_of_le_ne_top hP0 (ENNReal.tsum_le_tsum fun w => by
      simp only [hal, ha]; gcongr; exact EReal.toENNReal_le_toENNReal (hzl_le 0 w))
  have e1 : ∀ k, expect q (fun w => g x u w * J k (f x u w)) =
      ((∑' w, a k w : ENNReal) : EReal) - ((∑' w, b k w : ENNReal) : EReal) :=
    fun k => expect_of_ne_top q _ (hPk k)
  have e2 : expect q zl =
      ((∑' w, al w : ENNReal) : EReal) - ((∑' w, bl w : ENNReal) : EReal) :=
    expect_of_ne_top q _ hPl
  simp only [e1]
  rw [e2]
  have hc1 := continuous_coe_ennreal_ereal.tendsto _ |>.comp hPlim
  have hc2 := continuous_neg.tendsto _ |>.comp (continuous_coe_ennreal_ereal.tendsto _ |>.comp hQlim)
  have hadd := EReal.continuousAt_add (p := (((∑' w, al w : ENNReal) : EReal),
      -((∑' w, bl w : ENNReal) : EReal)))
    (Or.inl (by simpa using hPl)) (Or.inl (EReal.coe_ennreal_ne_bot _))
  simp only [sub_eq_add_neg]
  exact hadd.tendsto.comp (hc1.prodMk_nhds hc2)

theorem realB (t c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal (t + c) + ENNReal.ofReal (-t) =
      ENNReal.ofReal t + ENNReal.ofReal (-(t + c)) + ENNReal.ofReal c := by
  rcases le_total 0 t with ht | ht
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -t ≤ 0),
      ENNReal.ofReal_of_nonpos (by linarith : -(t + c) ≤ 0), ENNReal.ofReal_add ht hc]
    simp
  · rcases le_total 0 (t + c) with htc | htc
    · rw [ENNReal.ofReal_of_nonpos ht, ENNReal.ofReal_of_nonpos (by linarith : -(t + c) ≤ 0),
        ← ENNReal.ofReal_add htc (by linarith)]
      simp only [zero_add]; congr 1; ring
    · rw [ENNReal.ofReal_of_nonpos ht, ENNReal.ofReal_of_nonpos htc, zero_add, zero_add,
        ← ENNReal.ofReal_add (by linarith) hc]
      congr 1; ring

theorem ptB (z : EReal) (c : ℝ) (hc : 0 ≤ c) :
    (z + (c : EReal)).toENNReal + (-z).toENNReal =
      z.toENNReal + (-(z + (c : EReal))).toENNReal + ENNReal.ofReal c := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, EReal.real_coe_toENNReal,
      EReal.real_coe_toENNReal, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
    exact realB t c hc

theorem ptA (z : EReal) (c : ℝ) :
    (z + (c : EReal)).toENNReal ≤ z.toENNReal + ENNReal.ofReal c :=
  EReal.toENNReal_add_le.trans (le_of_eq (by rw [EReal.real_coe_toENNReal]))

theorem expect_add_le {W : Type*} (q : PMF W) (z : W → EReal) (c : W → ℝ)
    (hc0 : ∀ w, 0 ≤ c w) (B : ℝ) (hcB : ∀ w, c w ≤ B) :
    expect q (fun w => z w + (c w : EReal)) ≤ expect q z + (B : EReal) := by
  set P := ∑' w, q w * (z w).toENNReal with hP
  set Q := ∑' w, q w * (-(z w)).toENNReal with hQ
  set P' := ∑' w, q w * (z w + (c w : EReal)).toENNReal with hP'
  set Q' := ∑' w, q w * (-(z w + (c w : EReal))).toENNReal with hQ'
  set Cs := ∑' w, q w * ENNReal.ofReal (c w) with hCs
  have hCsB : Cs ≤ ENNReal.ofReal B := by
    calc Cs ≤ ∑' w, q w * ENNReal.ofReal B :=
          ENNReal.tsum_le_tsum fun w => by gcongr; exact hcB w
      _ = ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hCs_ne : Cs ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCsB
  have hEq : P' + Q = P + Q' + Cs := by
    simp only [hP', hQ, hP, hQ', hCs]
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1; funext w
    rw [← mul_add, ← mul_add, ← mul_add, ptB (z w) (c w) (hc0 w)]
  have hP'le : P' ≤ P + Cs := by
    simp only [hP', hP, hCs]
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun w => by rw [← mul_add]; gcongr; exact ptA _ _
  by_cases hPt : P = ⊤
  · have : expect q z = ⊤ := by simp only [expect]; rw [if_pos hPt]
    rw [this, EReal.top_add_coe]; exact le_top
  have hP't : P' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hPt, hCs_ne⟩) hP'le
  rw [expect_of_ne_top q _ hP't, expect_of_ne_top q _ hPt, ← hP', ← hQ', ← hP, ← hQ]
  by_cases hQt : Q = ⊤
  · have hQ't : Q' = ⊤ := by
      by_contra hne
      have : P' + Q ≠ ⊤ := by
        rw [hEq]; exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hPt, hne⟩, hCs_ne⟩
      rw [hQt] at this; simp at this
    rw [hQ't]; simp only [EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
  have hQ't : Q' ≠ ⊤ := by
    have : P + Q' + Cs ≠ ⊤ := by rw [← hEq]; exact ENNReal.add_ne_top.2 ⟨hP't, hQt⟩
    exact ne_top_of_le_ne_top this (le_trans le_add_self le_self_add)
  have hreal : P'.toReal + Q.toReal = P.toReal + Q'.toReal + Cs.toReal := by
    rw [← ENNReal.toReal_add hP't hQt, hEq, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hPt, hQ't⟩) hCs_ne,
      ENNReal.toReal_add hPt hQ't]
  have hCsr : Cs.toReal ≤ B := by
    have hB0 : 0 ≤ B := by
      obtain ⟨w, -⟩ := q.support_nonempty
      exact (hc0 w).trans (hcB w)
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCsB
    rwa [ENNReal.toReal_ofReal hB0] at this
  rw [← EReal.coe_ennreal_toReal hP't, ← EReal.coe_ennreal_toReal hQ't,
    ← EReal.coe_ennreal_toReal hPt, ← EReal.coe_ennreal_toReal hQt, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

theorem gmul_add (gr : ℝ) (hg : 0 ≤ gr) (y : EReal) (r : ℝ) :
    (gr : EReal) * (y + (r : EReal)) = (gr : EReal) * y + ((gr * r : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hg with h | h
  · subst h; simp
  induction y using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos h]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos h, EReal.top_add_coe]
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1; ring

theorem F2_core {S C W : Type*} (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) (b : ℝ)
    (hb : ∀ x, ∀ u ∈ m.U x, ∀ w, g x u w ≤ (b : EReal)) : m.F2With b := by
  intro r hr J x u hu
  refine ⟨m.mono x u hu _ _ fun y => le_add_of_nonneg_right (EReal.coe_nonneg.2 hr.le), ?_⟩
  rw [hH]
  simp only [multiplicativeH]
  have hgr : ∀ w, g x u w = ((g x u w).toReal : EReal) := fun w =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hb x u hu w))
      (ne_bot_of_le_ne_bot (by simp) (hg x u hu w))).symm
  have hg0 : ∀ w, 0 ≤ (g x u w).toReal := fun w => EReal.toReal_nonneg (hg x u hu w)
  have hgb : ∀ w, (g x u w).toReal ≤ b := fun w => by
    have := hb x u hu w; rw [hgr w] at this; exact EReal.coe_le_coe_iff.1 this
  have heq : (fun w => g x u w * (J (f x u w) + (r : EReal))) =
      fun w => g x u w * J (f x u w) + (((g x u w).toReal * r : ℝ) : EReal) := by
    funext w; rw [hgr w, gmul_add _ (hg0 w)]; simp only [EReal.toReal_coe]
  rw [heq]
  have := expect_add_le (p x u) (fun w => g x u w * J (f x u w)) (fun w => (g x u w).toReal * r)
    (fun w => mul_nonneg (hg0 w) hr.le) (b * r) (fun w => mul_le_mul_of_nonneg_right (hgb w) hr.le)
  exact this

end MulAux

theorem multiplicative_F1_F2_core {S C W : Type*} [Countable W] (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) :
    m.AssumptionF1 ∧
    ∀ b : ℝ, (∀ x, ∀ u ∈ m.U x, ∀ w, g x u w ≤ (b : EReal)) →
      m.AssumptionF2 ∧ m.F2With b := by
  refine ⟨MulAux.F1_core m p g f hg hH, fun b hb => ⟨?_, MulAux.F2_core m p g f hg hH b hb⟩⟩
  refine ⟨max b 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  exact MulAux.F2_core m p g f hg hH (max b 1) fun x u hu w =>
    (hb x u hu w).trans (EReal.coe_le_coe_iff.2 (le_max_left _ _))

end BertsekasShreve.FiniteHorizon

open BertsekasShreve.FiniteHorizon
open Model

theorem solution {S C W : Type*} [Countable W] (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) :
    m.AssumptionF1 ∧
    ∀ b : ℝ, (∀ x, ∀ u ∈ m.U x, ∀ w, g x u w ≤ (b : EReal)) →
      m.AssumptionF2 ∧ m.F2With b := by
  exact multiplicative_F1_F2_core m p g f hg hH
