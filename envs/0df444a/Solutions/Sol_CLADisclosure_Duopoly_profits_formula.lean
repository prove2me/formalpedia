-- Prove2me | solution 1 for CLADisclosure.Duopoly.profits_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:03:03.554209+00:00
-- url     : https://prove2.me/submissions/9616a3e1-cd76-475e-8331-e5339406f15c

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

set_option autoImplicit false
open MeasureTheory intervalIntegral CLADisclosure.Duopoly

namespace CLAH

noncomputable def fc (f : ℝ → ℝ) (x : ℝ) : ℝ := f (max 0 (min x 1))
noncomputable def Fc (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ q in (0:ℝ)..x, fc f q

section
variable {F f : ℝ → ℝ}

lemma clamp_mem (x : ℝ) : max 0 (min x 1) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma fc_eq (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : fc f x = f x := by
  simp [fc, min_eq_left hx.2, max_eq_right hx.1]

lemma fc_cont (hF : QualityDist F f) : Continuous (fc f) := by
  have : Continuous (fun x : ℝ => max 0 (min x 1)) := by fun_prop
  exact hF.cont.comp_continuous this clamp_mem

lemma fc_pos (hF : QualityDist F f) (x : ℝ) : 0 < fc f x := hF.pos _ (clamp_mem x)

lemma Fc_deriv (hF : QualityDist F f) (x : ℝ) : HasDerivAt (Fc f) (fc f x) x :=
  integral_hasDerivAt_right ((fc_cont hF).intervalIntegrable _ _)
    ((fc_cont hF).stronglyMeasurableAtFilter _ _) (fc_cont hF).continuousAt

lemma F_eq (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : F x = Fc f x := by
  rw [hF.cdf x hx, Fc]
  apply intervalIntegral.integral_congr
  intro q hq
  have : q ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le hx.1] at hq
    exact ⟨hq.1, hq.2.trans hx.2⟩
  simp [fc_eq q this]

lemma F_zero (hF : QualityDist F f) : F 0 = 0 := by
  rw [hF.cdf 0 ⟨le_rfl, zero_le_one⟩]; simp

lemma F_cont (hF : QualityDist F f) : ContinuousOn F (Set.Icc 0 1) := by
  have : ContinuousOn (Fc f) (Set.Icc 0 1) :=
    fun x _ => (Fc_deriv hF x).continuousAt.continuousWithinAt
  exact this.congr (fun x hx => F_eq hF hx)

lemma sub_mem {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    Set.uIcc a b ⊆ Set.Icc (0:ℝ) 1 := by
  intro x hx
  rw [Set.uIcc_eq_union] at hx
  rcases hx with hx | hx
  · exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  · exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩

lemma F_ii (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable F volume a b :=
  ((F_cont hF).mono (sub_mem ha hb)).intervalIntegrable

lemma f_ii (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable f volume a b :=
  (hF.cont.mono (sub_mem ha hb)).intervalIntegrable

lemma F_sub (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    F b - F a = ∫ q in a..b, f q := by
  rw [hF.cdf a ha, hF.cdf b hb]
  exact integral_interval_sub_left (f_ii hF ⟨le_rfl, zero_le_one⟩ hb) (f_ii hF ⟨le_rfl, zero_le_one⟩ ha) 

lemma F_strict (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hab : a < b) : F a < F b := by
  have := F_sub hF ha hb
  have hp : 0 < ∫ q in a..b, f q := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (f_ii hF ha hb) _ hab
    intro x hx
    exact hF.pos x ⟨ha.1.trans hx.1.le, hx.2.le.trans hb.2⟩
  linarith

lemma F_mono (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hab : a ≤ b) : F a ≤ F b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (F_strict hF ha hb h).le

lemma F_pos (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) : 0 < F x := by
  have := F_strict hF (a := 0) (b := x) ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩ hx.1
  rwa [F_zero hF] at this

lemma F_nonneg (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ F x := by
  rcases hx.1.eq_or_lt with h | h
  · rw [← h, F_zero hF]
  · exact (F_pos hF ⟨h, hx.2⟩).le

lemma F_le_one (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : F x ≤ 1 := by
  have := F_mono hF hx (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1) hx.2
  rwa [hF.total] at this

lemma F_lt_one (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) : F x < 1 := by
  have := F_strict hF (a := x) (b := 1) ⟨hx.1, hx.2.le⟩ ⟨zero_le_one, le_rfl⟩ hx.2
  rwa [hF.total] at this

lemma F_deriv (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) : HasDerivAt F (f x) x := by
  have h1 := Fc_deriv hF x
  rw [fc_eq x ⟨hx.1.le, hx.2.le⟩] at h1
  apply h1.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using F_eq hF ⟨hy.1.le, hy.2.le⟩


lemma Fc_cont (hF : QualityDist F f) : Continuous (Fc f) :=
  continuous_iff_continuousAt.2 fun x => (Fc_deriv hF x).continuousAt

lemma Phi_eq (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∫ q in (0:ℝ)..x, F q = ∫ q in (0:ℝ)..x, Fc f q := by
  apply intervalIntegral.integral_congr
  intro q hq
  exact F_eq hF (sub_mem ⟨le_rfl, zero_le_one⟩ hx hq)

lemma K1 (hF : QualityDist F f) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    ∫ q in a..b, q * f q = b * F b - a * F a - ∫ q in a..b, F q := by
  have hφ : ∀ x : ℝ, HasDerivAt (fun q => q * Fc f q - ∫ t in (0:ℝ)..q, Fc f t) (x * fc f x) x := by
    intro x
    have h1 := (hasDerivAt_id' x).mul (Fc_deriv hF x)
    have h2 : HasDerivAt (fun q => ∫ t in (0:ℝ)..q, Fc f t) (Fc f x) x :=
      integral_hasDerivAt_right ((Fc_cont hF).intervalIntegrable _ _)
        ((Fc_cont hF).stronglyMeasurableAtFilter _ _) (Fc_cont hF).continuousAt
    exact (h1.sub h2).congr_deriv (by ring)
  have h := integral_eq_sub_of_hasDerivAt (a := a) (b := b) (fun x _ => hφ x)
    ((continuous_id.mul (fc_cont hF)).intervalIntegrable _ _)
  have e1 : ∫ q in a..b, q * f q = ∫ q in a..b, q * fc f q := by
    apply intervalIntegral.integral_congr
    intro q hq
    simp only [fc_eq q (sub_mem ha hb hq)]
  have e2 : ∫ q in a..b, F q = (∫ q in (0:ℝ)..b, F q) - ∫ q in (0:ℝ)..a, F q :=
    (integral_interval_sub_left (F_ii hF ⟨le_rfl, zero_le_one⟩ hb)
      (F_ii hF ⟨le_rfl, zero_le_one⟩ ha)).symm ▸ rfl
  rw [e1, h, e2, Phi_eq hF ha, Phi_eq hF hb, F_eq hF ha, F_eq hF hb]
  ring

lemma Phi_pos (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    0 < ∫ q in (0:ℝ)..x, F q := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (F_ii hF ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩) _ hx.1
  intro q hq
  exact F_pos hF ⟨hq.1, hq.2.le.trans hx.2⟩

lemma Phi_lt (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    ∫ q in (0:ℝ)..x, F q < x * F x := by
  have h := K1 hF (a := 0) (b := x) ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩
  have hp : 0 < ∫ q in (0:ℝ)..x, q * f q := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hx.1
    · have : ContinuousOn (fun q => q * f q) (Set.Icc 0 1) := continuousOn_id.mul hF.cont
      exact (this.mono (sub_mem ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩)).intervalIntegrable
    · intro q hq
      exact mul_pos hq.1 (hF.pos q ⟨hq.1.le, hq.2.le.trans hx.2⟩)
  rw [h] at hp
  simp [F_zero hF] at hp
  linarith

lemma G_bounds (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    0 < Gfun F x ∧ Gfun F x < x := by
  have hFx := F_pos hF hx
  unfold Gfun
  constructor
  · exact div_pos (Phi_pos hF hx) hFx
  · rw [div_lt_iff₀ hFx]; exact Phi_lt hF hx

lemma m_mem (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    x - Gfun F x ∈ Set.Ioo (0:ℝ) x := by
  have := G_bounds hF hx
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

lemma m_mem' (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    x - Gfun F x ∈ Set.Ioc (0:ℝ) 1 :=
  ⟨(m_mem hF hx).1, (m_mem hF hx).2.le.trans hx.2⟩

lemma H_pos (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) : 0 < Hfun F x :=
  div_pos (Phi_pos hF (m_mem' hF hx)) (F_pos hF hx)

lemma condMean_eq' (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    condMean F f x = x - Gfun F x := by
  have hFx := F_pos hF hx
  have h := K1 hF (a := 0) (b := x) ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2⟩
  unfold condMean Gfun
  rw [h]
  field_simp
  simp [F_zero hF]


lemma ii_of_cont {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) : IntervalIntegrable h volume a b :=
  (hh.mono (sub_mem ha hb)).intervalIntegrable

lemma Icc_of_Ioc {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩

lemma zero_mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩

lemma int_f (hF : QualityDist F f) {b : ℝ} (hb : b ∈ Set.Icc (0:ℝ) 1) :
    ∫ q in (0:ℝ)..b, f q = F b := by
  have := F_sub hF (a := 0) (b := b) zero_mem hb
  rw [F_zero hF] at this; linarith

lemma K0 (hF : QualityDist F f) {b : ℝ} (hb : b ∈ Set.Icc (0:ℝ) 1) :
    ∫ q in (0:ℝ)..b, q * f q = b * F b - ∫ q in (0:ℝ)..b, F q := by
  rw [K1 hF zero_mem hb, F_zero hF]; ring

lemma K2 (hF : QualityDist F f) {b : ℝ} (hb : b ∈ Set.Icc (0:ℝ) 1) :
    ∫ q in (0:ℝ)..b, (b - q) * f q = ∫ q in (0:ℝ)..b, F q := by
  have h1 : IntervalIntegrable f volume 0 b := f_ii hF zero_mem hb
  have h2 : IntervalIntegrable (fun q => q * f q) volume 0 b :=
    ii_of_cont (continuousOn_id.mul hF.cont) zero_mem hb
  have : ∀ q : ℝ, (b - q) * f q = b * f q - q * f q := fun q => by ring
  simp_rw [this]
  rw [integral_sub (h1.const_mul b) h2, intervalIntegral.integral_const_mul, int_f hF hb, K0 hF hb]
  ring

lemma nondisc_eq (hF : QualityDist F f) {g l qh : ℝ} (hqh : qh ∈ Set.Ioc (0:ℝ) 1) :
    nondiscUtility F f g l qh = condMean F f qh - (l - g) * Hfun F qh := by
  have hFx := F_pos hF hqh
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have hqb : condMean F f qh = qh - Gfun F qh := condMean_eq' hF hqh
  have hm := m_mem hF hqh
  have hmI : qh - Gfun F qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc (m_mem' hF hqh)
  set qbar := condMean F f qh with hqbar
  have hpt : ∀ q, claUtility g l qbar q * f q =
      (1 + g) * (q * f q) - (g * qbar) * f q - (l - g) * (max (qbar - q) 0 * f q) := by
    intro q; unfold claUtility
    rcases le_total q qbar with h | h
    · rw [max_eq_right (by linarith : q - qbar ≤ 0), max_eq_left (by linarith : 0 ≤ qbar - q)]; ring
    · rw [max_eq_left (by linarith : 0 ≤ q - qbar), max_eq_right (by linarith : qbar - q ≤ 0)]; ring
  have hi1 : IntervalIntegrable f volume 0 qh := f_ii hF zero_mem hq
  have hi2 : IntervalIntegrable (fun q => q * f q) volume 0 qh :=
    ii_of_cont (continuousOn_id.mul hF.cont) zero_mem hq
  have hcm : ContinuousOn (fun q => max (qbar - q) 0 * f q) (Set.Icc 0 1) :=
    (((continuous_const.sub continuous_id).max continuous_const).continuousOn).mul hF.cont
  have hi3 : IntervalIntegrable (fun q => max (qbar - q) 0 * f q) volume 0 qh :=
    ii_of_cont hcm zero_mem hq
  have hI2 : ∫ q in (0:ℝ)..qh, max (qbar - q) 0 * f q = ∫ q in (0:ℝ)..qbar, F q := by
    have hqm : qbar ∈ Set.Icc (0:ℝ) 1 := by rw [hqb]; exact hmI
    have hqle : qbar ≤ qh := by rw [hqb]; linarith [hm.1, hm.2, (G_bounds hF hqh).1]
    rw [← integral_add_adjacent_intervals (b := qbar) (ii_of_cont hcm zero_mem hqm)
      (ii_of_cont hcm hqm hq)]
    have e1 : ∫ q in qbar..qh, max (qbar - q) 0 * f q = 0 := by
      have : ∫ q in qbar..qh, max (qbar - q) 0 * f q = ∫ q in qbar..qh, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro q hq'
        rw [Set.uIcc_of_le hqle] at hq'
        simp [max_eq_right (by linarith [hq'.1] : qbar - q ≤ 0)]
      simpa using this
    have e2 : ∫ q in (0:ℝ)..qbar, max (qbar - q) 0 * f q = ∫ q in (0:ℝ)..qbar, (qbar - q) * f q := by
      apply intervalIntegral.integral_congr
      intro q hq'
      rw [Set.uIcc_of_le hqm.1] at hq'
      simp [max_eq_left (by linarith [hq'.2] : 0 ≤ qbar - q)]
    rw [e1, e2, K2 hF hqm]; ring
  have hI1 : ∫ q in (0:ℝ)..qh, claUtility g l qbar q * f q =
      qbar * F qh - (l - g) * ∫ q in (0:ℝ)..qbar, F q := by
    simp_rw [hpt]
    rw [integral_sub ((hi2.const_mul (1+g)).sub (hi1.const_mul (g * qbar))) (hi3.const_mul (l - g)),
      integral_sub (hi2.const_mul (1+g)) (hi1.const_mul (g * qbar)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hI2, int_f hF hq, K0 hF hq]
    have : qbar * F qh = qh * F qh - ∫ q in (0:ℝ)..qh, F q := by
      rw [hqb]
      unfold Gfun
      field_simp
    rw [← this]; ring
  have hH : Hfun F qh * F qh = ∫ q in (0:ℝ)..qbar, F q := by
    rw [hqb]; unfold Hfun; field_simp
  unfold nondiscUtility
  rw [hI1]
  field_simp
  rw [← hH]; ring


noncomputable def Phic (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ q in (0:ℝ)..t, Fc f q
noncomputable def Lalt (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..1, Phic f t * fc f t) - (∫ t in (0:ℝ)..x, Phic f t * fc f t)
    - Phic f x * (1 - Fc f x)

lemma Phic_deriv (hF : QualityDist F f) (x : ℝ) : HasDerivAt (Phic f) (Fc f x) x :=
  integral_hasDerivAt_right ((Fc_cont hF).intervalIntegrable _ _)
    ((Fc_cont hF).stronglyMeasurableAtFilter _ _) (Fc_cont hF).continuousAt

lemma Phic_cont (hF : QualityDist F f) : Continuous (Phic f) :=
  continuous_iff_continuousAt.2 fun x => (Phic_deriv hF x).continuousAt

lemma Lalt_deriv (hF : QualityDist F f) (x : ℝ) :
    HasDerivAt (Lalt f) (-(Fc f x * (1 - Fc f x))) x := by
  have hc : Continuous (fun t => Phic f t * fc f t) := (Phic_cont hF).mul (fc_cont hF)
  have h1 : HasDerivAt (fun x => ∫ t in (0:ℝ)..x, Phic f t * fc f t) (Phic f x * fc f x) x :=
    integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  have h2 : HasDerivAt (fun x => Phic f x * (1 - Fc f x))
      (Fc f x * (1 - Fc f x) + Phic f x * (0 - fc f x)) x :=
    (Phic_deriv hF x).mul ((hasDerivAt_const x (1:ℝ)).sub (Fc_deriv hF x))
  have := ((hasDerivAt_const x (∫ t in (0:ℝ)..1, Phic f t * fc f t)).sub h1).sub h2
  exact this.congr_deriv (by ring)

lemma Lfun_eq (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Lfun F f x = Lalt f x := by
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : Continuous (fun t => Phic f t * fc f t) := (Phic_cont hF).mul (fc_cont hF)
  have e1 : Lfun F f x = ∫ qa in x..1, (Phic f qa * fc f qa - Phic f x * fc f qa) := by
    unfold Lfun
    apply intervalIntegral.integral_congr
    intro qa hqa
    have hq := sub_mem hx h1 hqa
    have : ∫ qb in x..qa, F qb = Phic f qa - Phic f x := by
      have := integral_interval_sub_left (F_ii hF zero_mem hq) (F_ii hF zero_mem hx)
      simp only [Phic]
      rw [← Phi_eq hF hq, ← Phi_eq hF hx, ← this]
    simp only
    rw [this, fc_eq qa hq]; ring
  have hFc1 : Fc f 1 = 1 := by rw [← F_eq hF h1, hF.total]
  have hfc : ∫ t in x..1, fc f t = 1 - Fc f x := by
    have := integral_interval_sub_left
      ((fc_cont hF).intervalIntegrable (μ := volume) 0 1)
      ((fc_cont hF).intervalIntegrable (μ := volume) 0 x)
    rw [← this]
    simp only [Fc] at hFc1 ⊢
    rw [hFc1]
  have hc2 : Continuous (fun t => Phic f x * fc f t) := continuous_const.mul (fc_cont hF)
  rw [e1, integral_sub (hc.intervalIntegrable x 1) (hc2.intervalIntegrable x 1),
    intervalIntegral.integral_const_mul, hfc,
    ← integral_interval_sub_left (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 0 x)]
  unfold Lalt
  ring


lemma L_deriv' (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (Lfun F f) (-(F x * (1 - F x))) x ∧ -(F x * (1 - F x)) < 0 := by
  have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  constructor
  · have h := Lalt_deriv hF x
    rw [← F_eq hF hxI] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using Lfun_eq hF ⟨hy.1.le, hy.2.le⟩
  · have h1 := F_pos hF (Set.mem_Ioc.2 ⟨hx.1, hx.2.le⟩)
    have h2 := F_lt_one hF (Set.mem_Ico.2 ⟨hx.1.le, hx.2⟩)
    have : 0 < F x * (1 - F x) := mul_pos h1 (by linarith)
    linarith

lemma L_cont (hF : QualityDist F f) : ContinuousOn (Lfun F f) (Set.Icc 0 1) := by
  have : ContinuousOn (Lalt f) (Set.Icc 0 1) :=
    fun x _ => (Lalt_deriv hF x).continuousAt.continuousWithinAt
  exact this.congr (fun x hx => Lfun_eq hF hx)


lemma int_split (hF : QualityDist F f) {g l qh : ℝ} (hqh : qh ∈ Set.Ioc (0:ℝ) 1) (a : ℝ) :
    ∫ qb in (0:ℝ)..1, margin a (rivalUtility F f g l qh qb) * f qb =
      max (a - nondiscUtility F f g l qh) 0 * F qh + ∫ qb in qh..1, max (a - qb) 0 * f qb := by
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set u := nondiscUtility F f g l qh with hu
  have hEa : Set.EqOn (fun qb => margin a (rivalUtility F f g l qh qb) * f qb)
      (fun qb => max (a - u) 0 * f qb) (Set.uIoc 0 qh) := by
    intro q hq'
    rw [Set.uIoc_of_le hqh.1.le] at hq'
    simp [margin, rivalUtility, hq'.2, hu]
  have hEb : Set.EqOn (fun qb => margin a (rivalUtility F f g l qh qb) * f qb)
      (fun qb => max (a - qb) 0 * f qb) (Set.uIoc qh 1) := by
    intro q hq'
    rw [Set.uIoc_of_le hqh.2] at hq'
    simp [margin, rivalUtility, not_le.2 hq'.1]
  have hcm : ContinuousOn (fun q => max (a - q) 0 * f q) (Set.Icc 0 1) :=
    (((continuous_const.sub continuous_id).max continuous_const).continuousOn).mul hF.cont
  have iiA : IntervalIntegrable (fun qb => margin a (rivalUtility F f g l qh qb) * f qb)
      volume 0 qh :=
    (intervalIntegrable_congr hEa).2 ((f_ii hF zero_mem hq).const_mul _)
  have iiB : IntervalIntegrable (fun qb => margin a (rivalUtility F f g l qh qb) * f qb)
      volume qh 1 :=
    (intervalIntegrable_congr hEb).2 (ii_of_cont hcm hq h1)
  rw [← integral_add_adjacent_intervals iiA iiB]
  congr 1
  · rw [intervalIntegral.integral_congr_ae (g := fun qb => max (a - u) 0 * f qb)
      (Filter.Eventually.of_forall (fun x hx => hEa hx)),
      intervalIntegral.integral_const_mul, int_f hF hq]
  · exact intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => hEb hx))

lemma u_le (hF : QualityDist F f) {g l qh : ℝ} (hk : g ≤ l) (hqh : qh ∈ Set.Ioc (0:ℝ) 1) :
    nondiscUtility F f g l qh ≤ qh := by
  rw [nondisc_eq hF hqh, condMean_eq' hF hqh]
  have := H_pos hF hqh
  have := (G_bounds hF hqh).1
  nlinarith

lemma u_eq (hF : QualityDist F f) {g l qh : ℝ} (hqh : qh ∈ Set.Ioc (0:ℝ) 1) :
    qh - nondiscUtility F f g l qh = Gfun F qh + (l - g) * Hfun F qh := by
  rw [nondisc_eq hF hqh, condMean_eq' hF hqh]; ring

lemma nondiscProfit_zero (hF : QualityDist F f) {g l qh : ℝ} (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0:ℝ) 1) : nondiscProfit F f g l qh = 0 := by
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have hu := u_le hF hk hqh
  unfold nondiscProfit
  rw [int_split hF hqh]
  have : ∫ qb in qh..1, max (nondiscUtility F f g l qh - qb) 0 * f qb = ∫ qb in qh..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro q hq'
    rw [Set.uIcc_of_le hqh.2] at hq'
    simp [max_eq_right (by linarith [hq'.1] : nondiscUtility F f g l qh - q ≤ 0)]
  rw [this]; simp

lemma int_tail (hF : QualityDist F f) {qh qa : ℝ} (hqh : qh ∈ Set.Ioc (0:ℝ) 1)
    (hqa : qa ∈ Set.Icc qh 1) :
    ∫ qb in qh..1, max (qa - qb) 0 * f qb = (∫ qb in qh..qa, F qb) - (qa - qh) * F qh := by
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have ha : qa ∈ Set.Icc (0:ℝ) 1 := ⟨hq.1.trans hqa.1, hqa.2⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hcm : ContinuousOn (fun q => max (qa - q) 0 * f q) (Set.Icc 0 1) :=
    (((continuous_const.sub continuous_id).max continuous_const).continuousOn).mul hF.cont
  rw [← integral_add_adjacent_intervals (b := qa) (ii_of_cont hcm hq ha) (ii_of_cont hcm ha h1)]
  have e1 : ∫ qb in qa..1, max (qa - qb) 0 * f qb = 0 := by
    have : ∫ qb in qa..1, max (qa - qb) 0 * f qb = ∫ qb in qa..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro q hq'
      rw [Set.uIcc_of_le hqa.2] at hq'
      simp [max_eq_right (by linarith [hq'.1] : qa - q ≤ 0)]
    simpa using this
  have e2 : ∫ qb in qh..qa, max (qa - qb) 0 * f qb = ∫ qb in qh..qa, ((qa * f qb) - qb * f qb) := by
    apply intervalIntegral.integral_congr
    intro q hq'
    rw [Set.uIcc_of_le hqa.1] at hq'
    simp only
    rw [max_eq_left (by linarith [hq'.2] : 0 ≤ qa - q)]; ring
  rw [e1, e2, integral_sub ((f_ii hF hq ha).const_mul qa)
    (ii_of_cont (h := fun q => q * f q) (continuousOn_id.mul hF.cont) hq ha),
    intervalIntegral.integral_const_mul,
    K1 hF hq ha, ← F_sub hF hq ha]
  ring

lemma disc_formula (hF : QualityDist F f) {g l c qh qa : ℝ} (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0:ℝ) 1) (hqa : qa ∈ Set.Icc qh 1) :
    discProfit F f g l c qh qa =
      F qh * (Gfun F qh + (l - g) * Hfun F qh) - c + ∫ qb in qh..qa, F qb := by
  have hu := u_le hF hk hqh
  have hu2 := u_eq hF (g := g) (l := l) hqh
  unfold discProfit
  rw [int_split hF hqh, int_tail hF hqh hqa, max_eq_left (by linarith [hqa.1])]
  rw [← hu2]; ring

lemma disc_le (hF : QualityDist F f) {g l c qh qa : ℝ} (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0:ℝ) 1) (hqa : qa ≤ qh) :
    discProfit F f g l c qh qa = max (qa - nondiscUtility F f g l qh) 0 * F qh - c := by
  unfold discProfit
  rw [int_split hF hqh]
  have : ∫ qb in qh..1, max (qa - qb) 0 * f qb = ∫ qb in qh..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro q hq'
    rw [Set.uIcc_of_le hqh.2] at hq'
    simp [max_eq_right (by linarith [hq'.1] : qa - q ≤ 0)]
  rw [this]; simp


lemma int_qa (hF : QualityDist F f) {qh qa : ℝ} (hqh : qh ∈ Set.Ioc (0:ℝ) 1)
    (hqa : qa ∈ Set.Icc qh 1) :
    ∫ qb in qh..qa, (qa - qb) * f qb = (∫ qb in qh..qa, F qb) - (qa - qh) * F qh := by
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have ha : qa ∈ Set.Icc (0:ℝ) 1 := ⟨hq.1.trans hqa.1, hqa.2⟩
  have e2 : ∫ qb in qh..qa, (qa - qb) * f qb = ∫ qb in qh..qa, ((qa * f qb) - qb * f qb) := by
    apply intervalIntegral.integral_congr
    intro q _
    simp only; ring
  rw [e2, integral_sub ((f_ii hF hq ha).const_mul qa)
    (ii_of_cont (h := fun q => q * f q) (continuousOn_id.mul hF.cont) hq ha),
    intervalIntegral.integral_const_mul, K1 hF hq ha, ← F_sub hF hq ha]
  ring

lemma profits_formula' (hF : QualityDist F f) {g l c qh : ℝ} (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0:ℝ) 1) :
    nondiscProfit F f g l qh = 0 ∧
    (∀ qa ∈ Set.Icc qh 1,
      discProfit F f g l c qh qa =
        (∫ qb in (0 : ℝ)..qh,
          (qa - condMean F f qh + (l - g) * Hfun F qh) * f qb) +
        (∫ qb in qh..qa, (qa - qb) * f qb) - c) := by
  refine ⟨nondiscProfit_zero hF hk hqh, fun qa hqa => ?_⟩
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  rw [disc_formula hF hk hqh hqa, intervalIntegral.integral_const_mul, int_f hF hq,
    int_qa hF hqh hqa, condMean_eq' hF hqh]
  ring

lemma inner_eq (hF : QualityDist F f) {x qa : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hq : qa ∈ Set.Icc (0:ℝ) 1) : ∫ qb in x..qa, F qb = Phic f qa - Phic f x := by
  have := integral_interval_sub_left (F_ii hF zero_mem hq) (F_ii hF zero_mem hx)
  simp only [Phic]
  rw [← Phi_eq hF hq, ← Phi_eq hF hx, ← this]

lemma eq_7' (hF : QualityDist F f) {g l c qh : ℝ} (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0 : ℝ) 1)
    (heq : F qh * (Gfun F qh + (l - g) * Hfun F qh) = c) :
    (∀ qa ∈ Set.Icc qh 1,
      discProfit F f g l c qh qa = ∫ qb in qh..qa, F qb) ∧
    exAnteProfit F f g l c qh = Lfun F f qh := by
  have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hD : ∀ qa ∈ Set.Icc qh 1, discProfit F f g l c qh qa = ∫ qb in qh..qa, F qb := by
    intro qa hqa
    rw [disc_formula hF hk hqh hqa, heq]; ring
  refine ⟨hD, ?_⟩
  unfold exAnteProfit Lfun
  set E2 : ℝ → ℝ := fun qa =>
    (if qa ≤ qh then nondiscProfit F f g l qh else discProfit F f g l c qh qa) * f qa with hE2
  have hEa : Set.EqOn E2 (fun _ => (0:ℝ)) (Set.uIoc 0 qh) := by
    intro q hq'
    rw [Set.uIoc_of_le hqh.1.le] at hq'
    simp [hE2, hq'.2, nondiscProfit_zero hF hk hqh]
  have hEb : Set.EqOn E2 (fun qa => (∫ qb in qh..qa, F qb) * f qa) (Set.uIoc qh 1) := by
    intro q hq'
    rw [Set.uIoc_of_le hqh.2] at hq'
    simp only [hE2, if_neg (not_le.2 hq'.1)]
    rw [hD q ⟨hq'.1.le, hq'.2⟩]
  have hT : Set.EqOn (fun qa => (∫ qb in qh..qa, F qb) * f qa)
      (fun qa => (Phic f qa - Phic f qh) * fc f qa) (Set.uIoc qh 1) := by
    intro q hq'
    rw [Set.uIoc_of_le hqh.2] at hq'
    have hqI : q ∈ Set.Icc (0:ℝ) 1 := ⟨hq.1.trans hq'.1.le, hq'.2⟩
    simp only
    rw [inner_eq hF hq hqI, fc_eq q hqI]
  have hcT : Continuous (fun qa => (Phic f qa - Phic f qh) * fc f qa) :=
    ((Phic_cont hF).sub continuous_const).mul (fc_cont hF)
  have iiA : IntervalIntegrable E2 volume 0 qh :=
    (intervalIntegrable_congr hEa).2 intervalIntegrable_const
  have iiT : IntervalIntegrable (fun qa => (∫ qb in qh..qa, F qb) * f qa) volume qh 1 :=
    (intervalIntegrable_congr hT).2 (hcT.intervalIntegrable _ _)
  have iiB : IntervalIntegrable E2 volume qh 1 := (intervalIntegrable_congr hEb).2 iiT
  rw [← integral_add_adjacent_intervals iiA iiB]
  have e1 : ∫ qa in (0:ℝ)..qh, E2 qa = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ))
      (Filter.Eventually.of_forall (fun x hx => hEa hx))]
    simp
  have e2 : ∫ qa in qh..1, E2 qa = ∫ qa in qh..1, (∫ qb in qh..qa, F qb) * f qa :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => hEb hx))
  rw [e1, e2, zero_add]


lemma eq_6' (hF : QualityDist F f) {g l c qh : ℝ} (hk : g ≤ l)
    (hcost : c < Gfun F 1 + (l - g) * Hfun F 1) :
    IsSymEqThreshold F f g l c qh ↔
      qh ∈ Set.Ioc (0 : ℝ) 1 ∧
        0 ≤ nondiscUtility F f g l qh ∧
        F qh * (Gfun F qh + (l - g) * Hfun F qh) = c := by
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  constructor
  · rintro ⟨hqh, hp, hsym⟩
    refine ⟨hqh, hp, ?_⟩
    have hq : qh ∈ Set.Icc (0:ℝ) 1 := Icc_of_Ioc hqh
    have hn := nondiscProfit_zero hF hk hqh
    have hle : F qh * (Gfun F qh + (l - g) * Hfun F qh) - c ≤ 0 := by
      have := (hsym qh ⟨hq.1, hq.2⟩).2 le_rfl
      rw [disc_formula hF hk hqh ⟨le_rfl, hq.2⟩, hn] at this
      simpa using this
    rcases hqh.2.eq_or_lt with h | h
    · exfalso
      subst h
      have hF1 : F 1 = 1 := hF.total
      rw [hF1] at hle
      linarith
    · have hge : 0 ≤ F qh * (Gfun F qh + (l - g) * Hfun F qh) - c := by
        by_contra hneg
        push Not at hneg
        set δ := c - F qh * (Gfun F qh + (l - g) * Hfun F qh) with hδ
        have hδp : 0 < δ := by linarith
        set qa := min 1 (qh + δ / 2) with hqa
        have hqa1 : qh < qa := lt_min h (by linarith)
        have hqa2 : qa ≤ qh + δ / 2 := min_le_right _ _
        have hqaI : qa ∈ Set.Icc qh 1 := ⟨hqa1.le, min_le_left _ _⟩
        have hqaI' : qa ∈ Set.Icc (0:ℝ) 1 := ⟨hq.1.trans hqa1.le, hqaI.2⟩
        have hnn := (hsym qa hqaI').1 hqa1
        rw [disc_formula hF hk hqh hqaI, hn] at hnn
        have hbound : ∫ qb in qh..qa, F qb ≤ ∫ qb in qh..qa, (1:ℝ) := by
          apply intervalIntegral.integral_mono_on hqa1.le (F_ii hF hq hqaI')
            intervalIntegrable_const
          intro x hx
          exact F_le_one hF ⟨hq.1.trans hx.1, hx.2.trans hqaI.2⟩
        simp at hbound
        linarith
      linarith
  · rintro ⟨hqh, hp, heq⟩
    refine ⟨hqh, hp, fun qa hqa => ⟨fun hlt => ?_, fun hle => ?_⟩⟩
    · have hqaI : qa ∈ Set.Icc qh 1 := ⟨hlt.le, hqa.2⟩
      rw [nondiscProfit_zero hF hk hqh, disc_formula hF hk hqh hqaI, heq]
      simp only [sub_self, zero_add]
      exact intervalIntegral.integral_nonneg hlt.le
        (fun x hx => F_nonneg hF ⟨(Icc_of_Ioc hqh).1.trans hx.1, hx.2.trans hqa.2⟩)
    · rw [nondiscProfit_zero hF hk hqh, disc_le hF hk hqh hle]
      have hFp := F_pos hF hqh
      have hu := u_eq hF (g := g) (l := l) hqh
      have : max (qa - nondiscUtility F f g l qh) 0 ≤ Gfun F qh + (l - g) * Hfun F qh := by
        apply max_le
        · linarith
        · rw [← hu]; linarith [u_le hF hk hqh]
      nlinarith


noncomputable def Gc (f : ℝ → ℝ) (x : ℝ) : ℝ := Phic f x / Fc f x
noncomputable def Hc (f : ℝ → ℝ) (x : ℝ) : ℝ := Phic f (x - Gc f x) / Fc f x

lemma Gfun_eq_Gc (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Gfun F x = Gc f x := by
  unfold Gfun Gc; rw [Phi_eq hF hx, F_eq hF hx]; rfl

lemma Hfun_eq_Hc (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    Hfun F x = Hc f x := by
  have hm := Icc_of_Ioc (m_mem' hF hx)
  have hG := Gfun_eq_Gc hF (Icc_of_Ioc hx)
  unfold Hfun Hc
  rw [hG] at hm ⊢
  rw [Phi_eq hF hm, F_eq hF (Icc_of_Ioc hx)]; rfl

lemma Fc_pos (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) : 0 < Fc f x := by
  rw [← F_eq hF (Icc_of_Ioc hx)]; exact F_pos hF hx

lemma Hc_cont (hF : QualityDist F f) : ContinuousOn (Hc f) (Set.Ioc 0 1) := by
  have hne : ∀ x ∈ Set.Ioc (0:ℝ) 1, Fc f x ≠ 0 := fun x hx => (Fc_pos hF hx).ne'
  have hG : ContinuousOn (Gc f) (Set.Ioc 0 1) :=
    (Phic_cont hF).continuousOn.div (Fc_cont hF).continuousOn hne
  unfold Hc
  exact ((Phic_cont hF).comp_continuousOn (continuousOn_id.sub hG)).div (Fc_cont hF).continuousOn hne

lemma Hc_deriv (hF : QualityDist F f) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (Hc f) (fc f x * Fc f (x - Gc f x) / (Fc f x) ^ 2 *
      (Gc f x - Gc f (x - Gc f x))) x := by
  have hx' : x ∈ Set.Ioc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hFx := Fc_pos hF hx'
  have hmI := m_mem' hF hx'
  have hGeq := Gfun_eq_Gc hF (Icc_of_Ioc hx')
  have hmI' : x - Gc f x ∈ Set.Ioc (0:ℝ) 1 := by rw [← hGeq]; exact hmI
  have hFm := Fc_pos hF hmI'
  have hG : HasDerivAt (Gc f) ((Fc f x * Fc f x - Phic f x * fc f x) / (Fc f x) ^ 2) x := by
    have := (Phic_deriv hF x).div (Fc_deriv hF x) hFx.ne'
    exact this
  have hm : HasDerivAt (fun y => y - Gc f y) (1 - (Fc f x * Fc f x - Phic f x * fc f x) / (Fc f x) ^ 2) x :=
    (hasDerivAt_id' x).sub hG
  have hP : HasDerivAt (fun y => Phic f (y - Gc f y))
      (Fc f (x - Gc f x) * (1 - (Fc f x * Fc f x - Phic f x * fc f x) / (Fc f x) ^ 2)) x :=
    HasDerivAt.comp (h₂ := Phic f) x (Phic_deriv hF _) hm
  have hH := hP.div (Fc_deriv hF x) hFx.ne'
  refine hH.congr_deriv ?_
  set m := x - Gc f x with hmdef
  have hgx : Gc f x = Phic f x / Fc f x := rfl
  have hgm : Gc f m = Phic f m / Fc f m := rfl
  rw [hgm, hgx]
  field_simp
  ring

lemma hfun_strictMono' (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1)) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (Hfun F)
        (f x * F (x - Gfun F x) / (F x) ^ 2 *
          (Gfun F x - Gfun F (x - Gfun F x))) x) ∧
    StrictMonoOn (Hfun F) (Set.Ioc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 < Hfun F x) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (Hfun F)
        (f x * F (x - Gfun F x) / (F x) ^ 2 *
          (Gfun F x - Gfun F (x - Gfun F x))) x := by
    intro x hx
    have hx' : x ∈ Set.Ioc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
    have hxI := Icc_of_Ioc hx'
    have hGeq := Gfun_eq_Gc hF hxI
    have hmI := m_mem' hF hx'
    have hmI' : x - Gc f x ∈ Set.Ioc (0:ℝ) 1 := by rw [← hGeq]; exact hmI
    have h := Hc_deriv hF hx
    have e1 : f x = fc f x := (fc_eq x hxI).symm
    have e2 : F x = Fc f x := F_eq hF hxI
    have e3 : F (x - Gfun F x) = Fc f (x - Gc f x) := by
      rw [hGeq]; exact F_eq hF (Icc_of_Ioc hmI')
    have e4 : Gfun F (x - Gfun F x) = Gc f (x - Gc f x) := by
      rw [hGeq]; rw [hGeq] at hmI; exact Gfun_eq_Gc hF (Icc_of_Ioc hmI')
    rw [e1, e2, e3, e4, hGeq]
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using Hfun_eq_Hc hF ⟨hy.1, hy.2.le⟩
  have hpos : ∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 < Hfun F x := fun x hx => H_pos hF hx
  refine ⟨hderiv, ?_, hpos⟩
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 1)
  · exact (Hc_cont hF).congr (fun x hx => Hfun_eq_Hc hF hx)
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hderiv x hx).deriv]
    have hx' : x ∈ Set.Ioc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
    have hmI := m_mem' hF hx'
    have hm := m_mem hF hx'
    have h1 : 0 < f x := hF.pos x ⟨hx.1.le, hx.2.le⟩
    have h2 : 0 < F (x - Gfun F x) := F_pos hF hmI
    have h3 : 0 < F x := F_pos hF hx'
    have h4 : Gfun F (x - Gfun F x) < Gfun F x := hG hmI hx' (by linarith [hm.2, (G_bounds hF hx').1])
    have := mul_pos (div_pos (mul_pos h1 h2) (pow_pos h3 2)) (sub_pos.2 h4)
    exact this


lemma Gc_cont (hF : QualityDist F f) : ContinuousOn (Gc f) (Set.Ioc 0 1) :=
  (Phic_cont hF).continuousOn.div (Fc_cont hF).continuousOn (fun x hx => (Fc_pos hF hx).ne')

lemma G_contOn (hF : QualityDist F f) : ContinuousOn (Gfun F) (Set.Ioc 0 1) :=
  (Gc_cont hF).congr (fun x hx => Gfun_eq_Gc hF (Icc_of_Ioc hx))

lemma H_contOn (hF : QualityDist F f) : ContinuousOn (Hfun F) (Set.Ioc 0 1) :=
  (Hc_cont hF).congr (fun x hx => Hfun_eq_Hc hF hx)

lemma Psi_strict (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1)) {k : ℝ} (hk : 0 ≤ k) :
    StrictMonoOn (fun x => F x * (Gfun F x + k * Hfun F x)) (Set.Ioc 0 1) := by
  have hH := (hfun_strictMono' hF hG).2.1
  intro x hx y hy hxy
  have hFx := F_pos hF hx
  have hS : 0 < Gfun F x + k * Hfun F x :=
    add_pos_of_pos_of_nonneg (G_bounds hF hx).1 (mul_nonneg hk (H_pos hF hx).le)
  have hFlt := F_strict hF (Icc_of_Ioc hx) (Icc_of_Ioc hy) hxy
  have hSlt : Gfun F x + k * Hfun F x < Gfun F y + k * Hfun F y :=
    add_lt_add_of_lt_of_le (hG hx hy hxy) (mul_le_mul_of_nonneg_left (hH hx hy hxy).le hk)
  exact mul_lt_mul'' hFlt hSlt hFx.le hS.le

lemma Psi_cont (hF : QualityDist F f) (k : ℝ) :
    ContinuousOn (fun x => F x * (Gfun F x + k * Hfun F x)) (Set.Ioc 0 1) :=
  ((F_cont hF).mono Set.Ioc_subset_Icc_self).mul
    ((G_contOn hF).add (continuousOn_const.mul (H_contOn hF)))

lemma Psi_small (hF : QualityDist F f) {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    F x * (Gfun F x + k * Hfun F x) ≤ (1 + k) * x := by
  have hFx := F_pos hF hx
  have hm := m_mem' hF hx
  have hmm := m_mem hF hx
  have e1 : F x * Gfun F x = ∫ q in (0:ℝ)..x, F q := by unfold Gfun; field_simp
  have e2 : F x * Hfun F x = ∫ q in (0:ℝ)..(x - Gfun F x), F q := by unfold Hfun; field_simp
  have i1 := Phi_lt hF hx
  have i2 := Phi_lt hF hm
  have f1 := F_le_one hF (Icc_of_Ioc hx)
  have f2 := F_le_one hF (Icc_of_Ioc hm)
  have : F x * (Gfun F x + k * Hfun F x) = (∫ q in (0:ℝ)..x, F q) +
      k * ∫ q in (0:ℝ)..(x - Gfun F x), F q := by rw [← e1, ← e2]; ring
  rw [this]
  have a1 : (∫ q in (0:ℝ)..x, F q) ≤ x := by nlinarith [hx.1]
  have a2 : (∫ q in (0:ℝ)..(x - Gfun F x), F q) ≤ x := by nlinarith [hmm.1, hmm.2]
  nlinarith

lemma claim_3' (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1))
    {g l c : ℝ} (hc : 0 < c) (hk : g ≤ l)
    (hcost : c < Gfun F 1 + (l - g) * Hfun F 1) :
    ∃! qh : ℝ, qh ∈ Set.Ioc (0 : ℝ) 1 ∧
      F qh * (Gfun F qh + (l - g) * Hfun F qh) = c := by
  have hk0 : 0 ≤ l - g := by linarith
  set k := l - g with hkdef
  have hmono := Psi_strict hF hG hk0
  have h1 : (1:ℝ) ∈ Set.Ioc (0:ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  set ε := min 1 (c / (2 * (1 + k))) with hε
  have hpos : 0 < c / (2 * (1 + k)) := div_pos hc (by linarith)
  have hε0 : 0 < ε := lt_min zero_lt_one hpos
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεI : ε ∈ Set.Ioc (0:ℝ) 1 := ⟨hε0, hε1⟩
  have hεc : (1 + k) * ε ≤ c / 2 := by
    have : ε ≤ c / (2 * (1 + k)) := min_le_right _ _
    have h2 : 0 < 1 + k := by linarith
    calc (1 + k) * ε ≤ (1 + k) * (c / (2 * (1 + k))) := mul_le_mul_of_nonneg_left this h2.le
      _ = c / 2 := by field_simp
  have hPε : F ε * (Gfun F ε + k * Hfun F ε) < c := by
    have := Psi_small hF hk0 hεI
    linarith
  have hP1 : F 1 * (Gfun F 1 + k * Hfun F 1) = Gfun F 1 + k * Hfun F 1 := by rw [hF.total]; ring
  have hcont : ContinuousOn (fun x => F x * (Gfun F x + k * Hfun F x)) (Set.Icc ε 1) :=
    (Psi_cont hF k).mono (fun x hx => ⟨hε0.trans_le hx.1, hx.2⟩)
  obtain ⟨qh, hqh, hqe⟩ := intermediate_value_Icc hε1 hcont
    ⟨hPε.le, by simp only [hP1]; exact hcost.le⟩
  refine ⟨qh, ⟨⟨hε0.trans_le hqh.1, hqh.2⟩, hqe⟩, ?_⟩
  rintro y ⟨hy, hye⟩
  exact hmono.injOn hy ⟨hε0.trans_le hqh.1, hqh.2⟩ (hye.trans hqe.symm)


lemma L_strictAnti (hF : QualityDist F f) : StrictAntiOn (Lfun F f) (Set.Ioc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · exact (L_cont hF).mono Set.Ioc_subset_Icc_self
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(L_deriv' hF hx).1.deriv]
    exact (L_deriv' hF hx).2

lemma proposition_2' (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1))
    {c g l₁ l₂ x₁ x₂ : ℝ} (hg : 0 < g)
    (hk₁ : g ≤ l₁) (hk : l₁ < l₂)
    (hcost : c < Gfun F 1 + (l₁ - g) * Hfun F 1)
    (h₁ : IsSymEqThreshold F f g l₁ c x₁)
    (h₂ : IsSymEqThreshold F f g l₂ c x₂) :
    x₂ < x₁ ∧ exAnteProfit F f g l₁ c x₁ < exAnteProfit F f g l₂ c x₂ := by
  have hk₂ : g ≤ l₂ := hk₁.trans hk.le
  have h1 : (1:ℝ) ∈ Set.Ioc (0:ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hcost₂ : c < Gfun F 1 + (l₂ - g) * Hfun F 1 := by
    have := H_pos hF h1
    nlinarith
  obtain ⟨hx₁, _, he₁⟩ := (eq_6' hF hk₁ hcost).1 h₁
  obtain ⟨hx₂, _, he₂⟩ := (eq_6' hF hk₂ hcost₂).1 h₂
  have hmono := Psi_strict hF hG (k := l₂ - g) (by linarith)
  have hlt : x₂ < x₁ := by
    by_contra hnot
    push Not at hnot
    have h := hmono.monotoneOn hx₁ hx₂ hnot
    have hH := H_pos hF hx₁
    have hFx := F_pos hF hx₁
    have : F x₁ * (Gfun F x₁ + (l₁ - g) * Hfun F x₁) <
        F x₁ * (Gfun F x₁ + (l₂ - g) * Hfun F x₁) := by
      apply mul_lt_mul_of_pos_left _ hFx
      nlinarith
    linarith
  refine ⟨hlt, ?_⟩
  rw [(eq_7' hF hk₁ hx₁ he₁).2, (eq_7' hF hk₂ hx₂ he₂).2]
  exact L_strictAnti hF hx₂ hx₁ hlt

end
end CLAH

theorem solution {F f : ℝ → ℝ} (hF : QualityDist F f)
    {g l c qh : ℝ} (hg : 0 < g) (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0 : ℝ) 1)
    (hp : 0 ≤ nondiscUtility F f g l qh) :
    nondiscProfit F f g l qh = 0 ∧
    (∀ qa ∈ Set.Icc qh 1,
      discProfit F f g l c qh qa =
        (∫ qb in (0 : ℝ)..qh,
          (qa - condMean F f qh + (l - g) * Hfun F qh) * f qb) +
        (∫ qb in qh..qa, (qa - qb) * f qb) - c) :=
  CLAH.profits_formula' hF hk hqh
