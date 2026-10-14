-- Prove2me | solution 1 for BertsekasShreve.Monotone.prop5_14_multiplicative_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:37:51.210041+00:00
-- url     : https://prove2.me/submissions/78603f58-bd41-4363-a296-209b9dc79eb2

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

open Filter Topology
open scoped ENNReal

namespace BertsekasShreve.Monotone

open BertsekasShreve.FiniteHorizon

theorem ml_tsum_iSup {W : Type*} [Countable W] (F : ℕ → W → ℝ≥0∞) (hF : Monotone F) :
    ∑' w, ⨆ k, F k w = ⨆ k, ∑' w, F k w := by
  letI : MeasurableSpace W := ⊤
  have h := MeasureTheory.lintegral_iSup (μ := MeasureTheory.Measure.count) (f := F)
    (fun n => measurable_from_top) hF
  rw [MeasureTheory.lintegral_count' measurable_from_top] at h
  simp only [MeasureTheory.lintegral_count' measurable_from_top] at h
  simpa [iSup_apply] using h

theorem ml_tsum_iInf {W : Type*} [Countable W] (F : ℕ → W → ℝ≥0∞) (hF : Antitone F)
    (hfin : ∑' w, F 0 w ≠ ⊤) :
    ∑' w, ⨅ k, F k w = ⨅ k, ∑' w, F k w := by
  letI : MeasurableSpace W := ⊤
  have h := MeasureTheory.lintegral_iInf (μ := MeasureTheory.Measure.count) (f := F)
    (fun n => measurable_from_top) hF (by rwa [MeasureTheory.lintegral_count' measurable_from_top])
  rw [MeasureTheory.lintegral_count' measurable_from_top] at h
  simp only [MeasureTheory.lintegral_count' measurable_from_top] at h
  simpa [iInf_apply] using h

theorem ml_expect_nonneg {W : Type*} (p : PMF W) (z : W → EReal) (hz : ∀ w, 0 ≤ z w) :
    expect p z = ((∑' w, p w * (z w).toENNReal : ℝ≥0∞) : EReal) := by
  have hQ : ∑' w, p w * (-(z w)).toENNReal = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun w => ?_
    rw [EReal.toENNReal_of_nonpos (by simpa using EReal.neg_le_neg_iff.2 (hz w)), mul_zero]
  unfold expect
  simp only
  rw [hQ]
  split_ifs with h
  · rw [h, EReal.coe_ennreal_top]
  · simp

theorem ml_one_ne_bot : (1 : EReal) ≠ ⊥ := by
  rw [← EReal.coe_one]; exact EReal.coe_ne_bot 1

theorem ml_toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [← EReal.coe_one, EReal.real_coe_toENNReal, ENNReal.ofReal_one]

theorem ml_contAt (a : ℝ) (ha : 0 < a) (s : EReal) :
    ContinuousAt (fun z : EReal => ((a : EReal) * z).toENNReal) s := by
  have h0 : (a : EReal) ≠ 0 := by exact_mod_cast ha.ne'
  have hmul : ContinuousAt (fun z : EReal => (a : EReal) * z) s := by
    have := EReal.continuousAt_mul (p := ((a : EReal), s)) (Or.inl h0) (Or.inl h0)
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))
    exact ContinuousAt.comp (f := fun z : EReal => ((a : EReal), z)) this
      (continuousAt_const.prodMk continuousAt_id)
  exact EReal.continuous_toENNReal.continuousAt.comp hmul

theorem ml_mono (a : ℝ) (ha : 0 ≤ a) : Monotone (fun z : EReal => ((a : EReal) * z).toENNReal) :=
  fun x y h => EReal.toENNReal_le_toENNReal (mul_le_mul_of_nonneg_left h (by exact_mod_cast ha))

theorem ml_map_iSup (a : ℝ) (ha : 0 < a) (c : ℕ → EReal) :
    ((a : EReal) * ⨆ k, c k).toENNReal = ⨆ k, ((a : EReal) * c k).toENNReal :=
  Monotone.map_iSup_of_continuousAt (f := fun z : EReal => ((a : EReal) * z).toENNReal)
    (ml_contAt a ha _) (ml_mono a ha.le) (by simp [EReal.coe_mul_bot_of_pos ha])

theorem mm_mul_add' {α : ℝ} (hα : 0 < α) (r : ℝ) {z : EReal} (hz : z ≠ ⊥) :
    (α : EReal) * (z + (r : EReal)) = (α : EReal) * z + ((α * r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => exact absurd rfl hz
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hα, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring

theorem ml_partA {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      ∀ b : ℝ, (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 1 ≤ g x u w ∧ g x u w ≤ (b : EReal)) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 b) := by
  intro m hH hJ b hg
  have hreal : ∀ x, ∀ u ∈ m.U x, ∀ w, g x u w = (((g x u w).toReal : ℝ) : EReal) := by
    intro x u hu w
    have h1 := (hg x u hu w).1
    have h2 := (hg x u hu w).2
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b) h2)
      (ne_bot_of_le_ne_bot ml_one_ne_bot h1)).symm
  have hpos : ∀ x, ∀ u ∈ m.U x, ∀ w, 1 ≤ (g x u w).toReal := by
    intro x u hu w
    have h1 := (hg x u hu w).1
    rw [hreal x u hu w] at h1
    exact_mod_cast h1
  have hle : ∀ x, ∀ u ∈ m.U x, ∀ w, (g x u w).toReal ≤ b := by
    intro x u hu w
    have h2 := (hg x u hu w).2
    rw [hreal x u hu w] at h2
    exact_mod_cast h2
  have hg0 : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w := fun x u hu w =>
    le_trans (by norm_num) (hg x u hu w).1
  refine ⟨?_, ?_, ?_⟩
  · intro x u hu
    rw [hH, hJ]
    show (1 : EReal) ≤ expect (p x u) (fun w => g x u w * 1)
    simp only [mul_one]
    rw [ml_expect_nonneg _ _ (hg0 x u hu)]
    have : (1 : EReal) = ((1 : ℝ≥0∞) : EReal) := by simp
    rw [this, EReal.coe_ennreal_le_coe_ennreal_iff, ← (p x u).tsum_coe]
    refine ENNReal.tsum_le_tsum fun w => ?_
    calc p x u w = p x u w * (1 : EReal).toENNReal := by rw [ml_toENNReal_one, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (EReal.toENNReal_le_toENNReal (hg x u hu w).1) (zero_le)
  · intro Js hJs hmono x u hu
    have hmon : Monotone Js := monotone_nat_of_le_succ hmono
    have hJs1 : ∀ k y, 0 ≤ Js k y := fun k y => by
      have := hJs k y; rw [hJ] at this; exact le_trans (by norm_num) this
    have hL : (fun y => limUnder atTop (fun k => Js k y)) = fun y => ⨆ k, Js k y := by
      funext y
      exact (tendsto_atTop_iSup (fun a b hab => hmon hab y)).limUnder_eq
    rw [hL]
    set F : ℕ → W → ℝ≥0∞ := fun k w =>
      p x u w * ((((g x u w).toReal : ℝ) : EReal) * Js k (f x u w)).toENNReal with hF
    have hFm : Monotone F := by
      intro a c hac w
      exact mul_le_mul_of_nonneg_left (ml_mono _ (by linarith [hpos x u hu w]) (hmon hac (f x u w))) (zero_le)
    have hk : ∀ k, m.H x u (Js k) = ((∑' w, F k w : ℝ≥0∞) : EReal) := by
      intro k
      rw [hH]
      show expect (p x u) (fun w => g x u w * Js k (f x u w)) = _
      rw [ml_expect_nonneg _ _ (fun w => mul_nonneg (hg0 x u hu w) (hJs1 k _))]
      congr 1
      refine tsum_congr fun w => ?_
      rw [hF]; simp only; rw [← hreal x u hu w]
    have hlim : m.H x u (fun y => ⨆ k, Js k y) = ((⨆ k, ∑' w, F k w : ℝ≥0∞) : EReal) := by
      rw [hH]
      show expect (p x u) (fun w => g x u w * ⨆ k, Js k (f x u w)) = _
      rw [ml_expect_nonneg _ _ (fun w => mul_nonneg (hg0 x u hu w)
        (le_trans (hJs1 0 _) (le_iSup (fun k => Js k (f x u w)) 0)))]
      congr 1
      rw [← ml_tsum_iSup F hFm]
      refine tsum_congr fun w => ?_
      rw [hreal x u hu w, ml_map_iSup _ (by linarith [hpos x u hu w]), ENNReal.mul_iSup]
    rw [hlim]
    simp only [hk]
    apply Tendsto.limUnder_eq
    exact (continuous_coe_ennreal_ereal.tendsto _).comp
      (tendsto_atTop_iSup (fun a c hac => ENNReal.tsum_le_tsum (hFm hac)))
  · obtain ⟨x0⟩ := m.S_nonempty
    obtain ⟨u0, hu0⟩ := m.U_nonempty x0
    obtain ⟨w0, -⟩ := (p x0 u0).support_nonempty
    have hb : 0 < b := by linarith [hpos x0 u0 hu0 w0, hle x0 u0 hu0 w0]
    refine ⟨hb, fun r hr J hJJ x u hu => ⟨?_, ?_⟩⟩
    · apply m.mono x u hu
      intro y
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)
    · have hJ0 : ∀ y, 0 ≤ J y := fun y => by
        have := hJJ y; rw [hJ] at this; exact le_trans (by norm_num) this
      rw [hH]
      show expect (p x u) (fun w => g x u w * (J (f x u w) + (r : EReal))) ≤
        expect (p x u) (fun w => g x u w * J (f x u w)) + _
      rw [ml_expect_nonneg _ _ (fun w => mul_nonneg (hg0 x u hu w) (hJ0 _)),
        ml_expect_nonneg _ _ (fun w => mul_nonneg (hg0 x u hu w)
          (le_trans (hJ0 _) (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le))))]
      have hbr : (((b * r : ℝ) : EReal)) = ((ENNReal.ofReal (b * r) : ℝ≥0∞) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
      rw [hbr, ← EReal.coe_ennreal_add, EReal.coe_ennreal_le_coe_ennreal_iff]
      calc ∑' w, p x u w * (g x u w * (J (f x u w) + (r : EReal))).toENNReal
          ≤ ∑' w, (p x u w * (g x u w * J (f x u w)).toENNReal + p x u w * ENNReal.ofReal (b * r)) := by
            refine ENNReal.tsum_le_tsum fun w => ?_
            rw [← mul_add]
            refine mul_le_mul_of_nonneg_left ?_ (zero_le)
            have hgp : 0 < (g x u w).toReal := by linarith [hpos x u hu w]
            rw [hreal x u hu w, mm_mul_add' hgp r (ne_bot_of_le_ne_bot (by simp) (hJ0 _)),
              EReal.toENNReal_add (mul_nonneg (by exact_mod_cast hgp.le) (hJ0 _))
                (by exact_mod_cast (by positivity : (0:ℝ) ≤ (g x u w).toReal * r)),
              EReal.real_coe_toENNReal]
            gcongr
            nlinarith [hle x u hu w]
        _ = _ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, (p x u).tsum_coe, one_mul]


theorem ml_expect_le {W : Type*} (p : PMF W) (z : W → EReal) (hz : ∀ w, z w ≤ 1) :
    (∑' w, p w * (z w).toENNReal ≤ 1) ∧
    expect p z = ((∑' w, p w * (z w).toENNReal : ℝ≥0∞) : EReal) -
      ((∑' w, p w * (-(z w)).toENNReal : ℝ≥0∞) : EReal) := by
  have hP : ∑' w, p w * (z w).toENNReal ≤ 1 := by
    rw [← p.tsum_coe]
    refine ENNReal.tsum_le_tsum fun w => ?_
    calc p w * (z w).toENNReal ≤ p w * (1 : EReal).toENNReal :=
          mul_le_mul_of_nonneg_left (EReal.toENNReal_le_toENNReal (hz w)) zero_le
      _ = p w := by rw [ml_toENNReal_one, mul_one]
  refine ⟨hP, ?_⟩
  unfold expect
  simp only
  rw [if_neg (ne_top_of_le_ne_top ENNReal.one_ne_top hP)]

theorem ml_ofReal_max (a : ℝ) : ENNReal.ofReal a = ENNReal.ofReal (max a 0) := by
  rcases le_total a 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem ml_id (z : EReal) {c : ℝ} (hc : 0 ≤ c) :
    (z - (c : EReal)).toENNReal + (-z).toENNReal + ENNReal.ofReal c =
      z.toENNReal + (-(z - (c : EReal))).toENNReal := by
  induction z using EReal.rec with
  | bot => simp [EReal.bot_sub]
  | top => simp [EReal.top_sub_coe]
  | coe x =>
    rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    rw [ml_ofReal_max (x - c), ml_ofReal_max (-x), ml_ofReal_max x, ml_ofReal_max (-(x - c)),
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (by positivity) hc,
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    congr 1
    rcases le_total c x with h1 | h1
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - c), max_eq_right (by linarith : -x ≤ 0),
        max_eq_left (by linarith : (0:ℝ) ≤ x), max_eq_right (by linarith : -(x - c) ≤ 0)]
      ring
    · rcases le_total 0 x with h2 | h2
      · rw [max_eq_right (by linarith : x - c ≤ 0), max_eq_right (by linarith : -x ≤ 0),
          max_eq_left h2, max_eq_left (by linarith : (0:ℝ) ≤ -(x - c))]
        ring
      · rw [max_eq_right (by linarith : x - c ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ -x),
          max_eq_right h2, max_eq_left (by linarith : (0:ℝ) ≤ -(x - c))]
        ring

theorem ml_expect_sub {W : Type*} (p : PMF W) (z : W → EReal) (c : W → ℝ) (r : ℝ) (hr : 0 < r)
    (hc0 : ∀ w, 0 ≤ c w) (hcr : ∀ w, c w ≤ r) (hz : ∀ w, z w ≤ 1) :
    expect p z - (r : EReal) ≤ expect p (fun w => z w - (c w : EReal)) := by
  have hz' : ∀ w, z w - (c w : EReal) ≤ 1 := fun w => by
    refine le_trans ?_ (hz w)
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (hc0 w))
  obtain ⟨hP, e1⟩ := ml_expect_le p z hz
  obtain ⟨hP', e2⟩ := ml_expect_le p _ hz'
  rw [e1, e2]
  set P := ∑' w, p w * (z w).toENNReal
  set Q := ∑' w, p w * (-(z w)).toENNReal
  set P' := ∑' w, p w * (z w - (c w : EReal)).toENNReal
  set Q' := ∑' w, p w * (-(z w - (c w : EReal))).toENNReal
  set Cc := ∑' w, p w * ENNReal.ofReal (c w)
  have hid : P' + Q + Cc = P + Q' := by
    simp only [P', Q, Cc, P, Q', ← ENNReal.tsum_add, ← mul_add]
    exact tsum_congr fun w => by rw [ml_id (z w) (hc0 w)]
  have hC : Cc ≤ ENNReal.ofReal r := by
    calc Cc ≤ ∑' w, p w * ENNReal.ofReal r :=
          ENNReal.tsum_le_tsum fun w => mul_le_mul_of_nonneg_left
            (ENNReal.ofReal_le_ofReal (hcr w)) zero_le
      _ = ENNReal.ofReal r := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
  by_cases hQ : Q = ⊤
  · rw [hQ, EReal.coe_ennreal_top, EReal.sub_top, EReal.bot_sub]
    exact bot_le
  have hPf : P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hP
  have hP'f : P' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hP'
  have hCf : Cc ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC
  have hQ'f : Q' ≠ ⊤ := by
    have : Q' ≤ P' + Q + Cc := hid ▸ le_add_self
    exact ne_top_of_le_ne_top (by simp [hP'f, hQ, hCf]) this
  have hreal : P'.toReal + Q.toReal + Cc.toReal = P.toReal + Q'.toReal := by
    rw [← ENNReal.toReal_add hP'f hQ, ← ENNReal.toReal_add (by simp [hP'f, hQ]) hCf,
      ← ENNReal.toReal_add hPf hQ'f, hid]
  have hCr : Cc.toReal ≤ r := ENNReal.toReal_le_of_le_ofReal hr.le hC
  rw [← EReal.coe_ennreal_toReal hPf, ← EReal.coe_ennreal_toReal hQ, ← EReal.coe_ennreal_toReal hP'f,
    ← EReal.coe_ennreal_toReal hQ'f, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
  exact_mod_cast (by linarith : P.toReal - Q.toReal - r ≤ P'.toReal - Q'.toReal)

theorem ml_mul_sub {a : ℝ} (ha : 0 ≤ a) (r : ℝ) {z : EReal} (hz : z ≠ ⊤) :
    (a : EReal) * (z - (r : EReal)) = (a : EReal) * z - ((a * r : ℝ) : EReal) := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  induction z using EReal.rec with
  | bot => rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos h, EReal.bot_sub]
  | top => exact absurd rfl hz
  | coe x => rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub]; congr 1; ring

theorem ml_map_iInf (a : ℝ) (ha : 0 ≤ a) (c : ℕ → EReal) :
    ((a : EReal) * ⨅ k, c k).toENNReal = ⨅ k, ((a : EReal) * c k).toENNReal := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  exact Monotone.map_iInf_of_continuousAt (f := fun z : EReal => ((a : EReal) * z).toENNReal)
    (ml_contAt a h _) (ml_mono a ha) (by simp [EReal.coe_mul_top_of_pos h])

theorem ml_map_iInf_neg (a : ℝ) (ha : 0 ≤ a) (c : ℕ → EReal) :
    (-((a : EReal) * ⨅ k, c k)).toENNReal = ⨆ k, (-((a : EReal) * c k)).toENNReal := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  have h0 : (a : EReal) ≠ 0 := by exact_mod_cast h.ne'
  have hmul : ∀ s, ContinuousAt (fun z : EReal => (a : EReal) * z) s := by
    intro s
    have := EReal.continuousAt_mul (p := ((a : EReal), s)) (Or.inl h0) (Or.inl h0)
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))
    exact ContinuousAt.comp (f := fun z : EReal => ((a : EReal), z)) this
      (continuousAt_const.prodMk continuousAt_id)
  refine Antitone.map_iInf_of_continuousAt (f := fun z : EReal => (-((a : EReal) * z)).toENNReal)
    ?_ ?_ ?_
  · exact EReal.continuous_toENNReal.continuousAt.comp
      (continuous_neg.continuousAt.comp (hmul _))
  · intro x y hxy
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2
      (mul_le_mul_of_nonneg_left hxy (by exact_mod_cast ha)))
  · simp [EReal.coe_mul_top_of_pos h]

theorem ml_partB {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ 1) →
        m.AssumptionD ∧ m.AssumptionD1 ∧ m.AssumptionD2 1) := by
  intro m hH hJ hg
  have hreal : ∀ x, ∀ u ∈ m.U x, ∀ w, g x u w = (((g x u w).toReal : ℝ) : EReal) := by
    intro x u hu w
    have h1 := (hg x u hu w).1
    have h2 := (hg x u hu w).2
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1) h2)
      (ne_bot_of_le_ne_bot (by simp) h1)).symm
  have hnn : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ (g x u w).toReal := by
    intro x u hu w
    have h1 := (hg x u hu w).1
    rw [hreal x u hu w] at h1
    exact_mod_cast h1
  have hle1 : ∀ x, ∀ u ∈ m.U x, ∀ w, (g x u w).toReal ≤ 1 := by
    intro x u hu w
    have h2 := (hg x u hu w).2
    rw [hreal x u hu w] at h2
    exact_mod_cast h2
  have hz1 : ∀ x, ∀ u ∈ m.U x, ∀ J : S → EReal, J ≤ m.Jbar → ∀ w, g x u w * J (f x u w) ≤ 1 := by
    intro x u hu J hJJ w
    have hJ1 : J (f x u w) ≤ 1 := by have := hJJ (f x u w); rw [hJ] at this; exact this
    calc g x u w * J (f x u w) ≤ g x u w * 1 :=
          mul_le_mul_of_nonneg_left hJ1 (hg x u hu w).1
      _ = g x u w := mul_one _
      _ ≤ 1 := (hg x u hu w).2
  refine ⟨?_, ?_, ?_⟩
  · intro x u hu
    rw [hH, hJ]
    show expect (p x u) (fun w => g x u w * 1) ≤ 1
    simp only [mul_one]
    obtain ⟨hP, -⟩ := ml_expect_le (p x u) (fun w => g x u w) (fun w => (hg x u hu w).2)
    rw [ml_expect_nonneg _ _ (fun w => (hg x u hu w).1)]
    have : (1 : EReal) = ((1 : ℝ≥0∞) : EReal) := by simp
    rw [this, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact hP
  · intro Js hJs hanti x u hu
    have hant : Antitone Js := antitone_nat_of_succ_le hanti
    have hL : (fun y => limUnder atTop (fun k => Js k y)) = fun y => ⨅ k, Js k y := by
      funext y
      exact (tendsto_atTop_iInf (fun a b hab => hant hab y)).limUnder_eq
    rw [hL]
    set a : W → ℝ := fun w => (g x u w).toReal with ha
    set Pk : ℕ → ℝ≥0∞ := fun k => ∑' w, p x u w * (((a w : ℝ) : EReal) * Js k (f x u w)).toENNReal
    set Qk : ℕ → ℝ≥0∞ := fun k => ∑' w, p x u w * (-(((a w : ℝ) : EReal) * Js k (f x u w))).toENNReal
    have hgz : ∀ w, g x u w = ((a w : ℝ) : EReal) := fun w => hreal x u hu w
    have hk : ∀ k, m.H x u (Js k) = (Pk k : EReal) - (Qk k : EReal) := by
      intro k
      rw [hH]
      show expect (p x u) (fun w => g x u w * Js k (f x u w)) = _
      rw [(ml_expect_le _ _ (hz1 x u hu (Js k) (hJs k))).2]
      simp only [Pk, Qk, hgz]
    have hlimv : m.H x u (fun y => ⨅ k, Js k y) =
        ((⨅ k, Pk k : ℝ≥0∞) : EReal) - ((⨆ k, Qk k : ℝ≥0∞) : EReal) := by
      rw [hH]
      show expect (p x u) (fun w => g x u w * ⨅ k, Js k (f x u w)) = _
      rw [(ml_expect_le _ _ (hz1 x u hu _ (fun y => (iInf_le (fun k => Js k y) 0).trans (hJs 0 y)))).2]
      congr 2
      · simp only [Pk, hgz]
        rw [← ml_tsum_iInf]
        · refine tsum_congr fun w => ?_
          rw [ml_map_iInf _ (hnn x u hu w), ENNReal.mul_iInf (fun h => absurd h (PMF.apply_ne_top _ _))]
        · intro i j hij w
          exact mul_le_mul_of_nonneg_left (ml_mono _ (hnn x u hu w) (hant hij _)) zero_le
        · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
          have := (ml_expect_le (p x u) _ (hz1 x u hu (Js 0) (hJs 0))).1
          simpa only [hgz] using this
      · simp only [Qk, hgz]
        rw [← ml_tsum_iSup]
        · refine tsum_congr fun w => ?_
          rw [ml_map_iInf_neg _ (hnn x u hu w), ENNReal.mul_iSup]
        · intro i j hij w
          refine mul_le_mul_of_nonneg_left (EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2
            (mul_le_mul_of_nonneg_left (hant hij _) (by exact_mod_cast hnn x u hu w)))) zero_le
    rw [hlimv]
    simp only [hk]
    apply Tendsto.limUnder_eq
    have hPanti : Antitone Pk := fun i j hij => ENNReal.tsum_le_tsum fun w =>
      mul_le_mul_of_nonneg_left (ml_mono _ (hnn x u hu w) (hant hij _)) zero_le
    have hQmono : Monotone Qk := fun i j hij => ENNReal.tsum_le_tsum fun w =>
      mul_le_mul_of_nonneg_left (EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2
        (mul_le_mul_of_nonneg_left (hant hij _) (by exact_mod_cast hnn x u hu w)))) zero_le
    have hP1 : (⨅ k, Pk k) ≤ 1 := by
      refine (iInf_le _ 0).trans ?_
      have := (ml_expect_le (p x u) _ (hz1 x u hu (Js 0) (hJs 0))).1
      simpa only [hgz] using this
    have tP : Tendsto (fun k => (Pk k : EReal)) atTop (𝓝 ((⨅ k, Pk k : ℝ≥0∞) : EReal)) :=
      (continuous_coe_ennreal_ereal.tendsto _).comp (tendsto_atTop_iInf hPanti)
    have tQ : Tendsto (fun k => -(Qk k : EReal)) atTop (𝓝 (-((⨆ k, Qk k : ℝ≥0∞) : EReal))) :=
      (continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp
        (tendsto_atTop_iSup hQmono))
    have hcont := EReal.continuousAt_add
      (p := (((⨅ k, Pk k : ℝ≥0∞) : EReal), -((⨆ k, Qk k : ℝ≥0∞) : EReal)))
      (Or.inl (by rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact ne_top_of_le_ne_top ENNReal.one_ne_top hP1))
      (Or.inl (ne_bot_of_le_ne_bot (by simp) (EReal.coe_ennreal_nonneg _)))
    have := hcont.tendsto.comp (tP.prodMk_nhds tQ)
    have h2 : (fun k => (Pk k : EReal) - (Qk k : EReal)) =
        (fun q : EReal × EReal => q.1 + q.2) ∘ (fun k => ((Pk k : EReal), -(Qk k : EReal))) := by
      funext k; simp [sub_eq_add_neg]
    rw [h2, sub_eq_add_neg]
    exact this
  · refine ⟨one_pos, fun r hr J hJJ x u hu => ⟨?_, ?_⟩⟩
    · have hJt : ∀ y, J y ≠ ⊤ := fun y => by
        have := hJJ y; rw [hJ] at this
        exact ne_top_of_le_ne_top (by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1) this
      rw [hH]
      show expect (p x u) (fun w => g x u w * J (f x u w)) - (((1 * r : ℝ)) : EReal) ≤
        expect (p x u) (fun w => g x u w * (J (f x u w) - (r : EReal)))
      have heq : (fun w => g x u w * (J (f x u w) - (r : EReal))) =
          fun w => g x u w * J (f x u w) - (((g x u w).toReal * r : ℝ) : EReal) := by
        funext w
        rw [hreal x u hu w, ml_mul_sub (hnn x u hu w) r (hJt _), EReal.toReal_coe]
      rw [heq, one_mul]
      exact ml_expect_sub (p x u) _ (fun w => (g x u w).toReal * r) r hr
        (fun w => mul_nonneg (hnn x u hu w) hr.le)
        (fun w => by nlinarith [hle1 x u hu w, hnn x u hu w])
        (hz1 x u hu J hJJ)
    · apply m.mono x u hu
      intro y
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot r)) (Or.inl (EReal.coe_ne_top r))]
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hr.le)

theorem prop5_14_core {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      ∀ b : ℝ, (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 1 ≤ g x u w ∧ g x u w ≤ (b : EReal)) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 b) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ 1) →
        m.AssumptionD ∧ m.AssumptionD1 ∧ m.AssumptionD2 1) :=
  ⟨ml_partA p g f, ml_partB p g f⟩

end BertsekasShreve.Monotone

open BertsekasShreve.Monotone


theorem solution {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      ∀ b : ℝ, (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 1 ≤ g x u w ∧ g x u w ≤ (b : EReal)) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 b) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ 1) →
        m.AssumptionD ∧ m.AssumptionD1 ∧ m.AssumptionD2 1) := by
  exact prop5_14_core p g f
