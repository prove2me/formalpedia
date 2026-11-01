-- Prove2me | solution 1 for DeferredInspection.SingleAgent.euler_lagrange_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:14:49.136333+00:00
-- url     : https://prove2.me/submissions/bef4c90b-1201-43a9-bcc4-562fcbcd5065

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

namespace DIThm2

lemma f_contOn {f : ℝ → ℝ} (hf : Assumption1 f) : ContinuousOn f (Icc 0 1) :=
  hf.1.continuousOn

lemma f_pos {f : ℝ → ℝ} (hf : Assumption1 f) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : 0 < f v :=
  hf.2.1 v hv

lemma yf_contOn {f : ℝ → ℝ} (hf : Assumption1 f) : ContinuousOn (fun y => y * f y) (Icc 0 1) :=
  continuousOn_id.mul (f_contOn hf)

lemma yf_ii {f : ℝ → ℝ} (hf : Assumption1 f) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) : IntervalIntegrable (fun y => y * f y) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (yf_contOn hf).mono
  exact uIcc_subset_Icc ha hb

lemma G_zero (f : ℝ → ℝ) : G f 0 = 0 := by simp [G]

lemma G_sub {f : ℝ → ℝ} (hf : Assumption1 f) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) : G f b - G f a = ∫ y in a..b, y * f y := by
  unfold G
  rw [intervalIntegral.integral_interval_sub_left (yf_ii hf ⟨le_rfl, zero_le_one⟩ hb)
    (yf_ii hf ⟨le_rfl, zero_le_one⟩ ha)]

lemma G_strictMonoOn {f : ℝ → ℝ} (hf : Assumption1 f) : StrictMonoOn (G f) (Icc 0 1) := by
  intro a ha b hb hab
  have := G_sub hf ha hb
  have hpos : 0 < ∫ y in a..b, y * f y := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (yf_ii hf ha hb) _ hab
    intro y hy
    have hy' : y ∈ Icc (0:ℝ) 1 := ⟨by linarith [ha.1, hy.1], by linarith [hb.2, hy.2]⟩
    exact mul_pos (by linarith [ha.1, hy.1]) (f_pos hf hy')
  linarith

lemma G_contOn {f : ℝ → ℝ} (hf : Assumption1 f) : ContinuousOn (G f) (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (a := 0)
    (yf_ii hf ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩) (by simp)
  rw [uIcc_of_le zero_le_one] at h
  exact h

lemma G_hasDerivAt {f : ℝ → ℝ} (hf : Assumption1 f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (G f) (t * f t) t := by
  have hc : ContinuousAt (fun y => y * f y) t :=
    (yf_contOn hf).continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hmeas : StronglyMeasurableAtFilter (fun y => y * f y) (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ((yf_contOn hf).mono Ioo_subset_Icc_self) t ht
  exact intervalIntegral.integral_hasDerivAt_right
    (yf_ii hf ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩) hmeas hc

lemma G_one_pos {f : ℝ → ℝ} (hf : Assumption1 f) : 0 < G f 1 := by
  have := G_strictMonoOn hf ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  rwa [G_zero] at this

lemma G_mem {f : ℝ → ℝ} (hf : Assumption1 f) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    G f y ∈ Icc 0 (G f 1) := by
  constructor
  · rw [← G_zero f]; exact (G_strictMonoOn hf).monotoneOn ⟨le_rfl, zero_le_one⟩ hy hy.1
  · exact (G_strictMonoOn hf).monotoneOn hy ⟨zero_le_one, le_rfl⟩ hy.2

/-! ### The lower inverse `Ginv` -/

lemma Ginv_G {f : ℝ → ℝ} (hf : Assumption1 f) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    Ginv f (G f y) = y := by
  unfold Ginv
  apply IsLeast.csInf_eq
  refine ⟨⟨hy, le_rfl⟩, ?_⟩
  rintro z ⟨hz, hzle⟩
  by_contra hlt
  push Not at hlt
  have := G_strictMonoOn hf hz hy hlt
  linarith

lemma exists_G_eq {f : ℝ → ℝ} (hf : Assumption1 f) {s : ℝ} (hs : s ∈ Icc 0 (G f 1)) :
    ∃ y ∈ Icc (0:ℝ) 1, G f y = s := by
  have h := intermediate_value_Icc (zero_le_one' ℝ) (G_contOn hf)
  rw [G_zero] at h
  exact h hs

lemma Ginv_mem {f : ℝ → ℝ} (hf : Assumption1 f) {s : ℝ} (hs : s ∈ Icc 0 (G f 1)) :
    Ginv f s ∈ Icc (0:ℝ) 1 := by
  obtain ⟨y, hy, rfl⟩ := exists_G_eq hf hs
  rw [Ginv_G hf hy]; exact hy

lemma G_Ginv {f : ℝ → ℝ} (hf : Assumption1 f) {s : ℝ} (hs : s ∈ Icc 0 (G f 1)) :
    G f (Ginv f s) = s := by
  obtain ⟨y, hy, rfl⟩ := exists_G_eq hf hs
  rw [Ginv_G hf hy]

lemma Ginv_strictMonoOn {f : ℝ → ℝ} (hf : Assumption1 f) :
    StrictMonoOn (Ginv f) (Icc 0 (G f 1)) := by
  intro a ha b hb hab
  by_contra hle
  push Not at hle
  have := (G_strictMonoOn hf).monotoneOn (Ginv_mem hf hb) (Ginv_mem hf ha) hle
  rw [G_Ginv hf ha, G_Ginv hf hb] at this
  linarith

lemma Ginv_zero {f : ℝ → ℝ} (hf : Assumption1 f) : Ginv f 0 = 0 := by
  have := Ginv_G hf (y := 0) ⟨le_rfl, zero_le_one⟩
  rwa [G_zero] at this

lemma Ginv_top {f : ℝ → ℝ} (hf : Assumption1 f) : Ginv f (G f 1) = 1 :=
  Ginv_G hf ⟨zero_le_one, le_rfl⟩

lemma Ginv_contOn {f : ℝ → ℝ} (hf : Assumption1 f) : ContinuousOn (Ginv f) (Icc 0 (G f 1)) := by
  set M := G f 1
  have hM : 0 ≤ M := (G_one_pos hf).le
  let P : ℝ → ℝ := fun s => max 0 (min s M)
  have hPmem : ∀ s, P s ∈ Icc 0 M := fun s => ⟨le_max_left _ _, max_le hM (min_le_right _ _)⟩
  have hPmono : Monotone P := fun a b hab => max_le_max le_rfl (min_le_min hab le_rfl)
  let h : ℝ → ℝ := fun s => Ginv f (P s) + (s - P s)
  have hmono : Monotone h := by
    intro a b hab
    have h1 : Ginv f (P a) ≤ Ginv f (P b) :=
      (Ginv_strictMonoOn hf).monotoneOn (hPmem a) (hPmem b) (hPmono hab)
    have h2 : a - P a ≤ b - P b := by
      simp only [P]
      rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
      rcases le_total a M with ha' | ha' <;> rcases le_total b M with hb' | hb' <;>
      simp [*, min_eq_left, min_eq_right, max_eq_left, max_eq_right] <;> linarith
    show Ginv f (P a) + (a - P a) ≤ Ginv f (P b) + (b - P b)
    linarith
  have hsurj : Function.Surjective h := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · refine ⟨t, ?_⟩
      have : P t = 0 := by simp only [P]; rw [min_eq_left (by linarith)]; exact max_eq_left ht.le
      simp only [h, this, Ginv_zero hf]; ring
    rcases le_or_gt t 1 with ht1 | ht1
    · refine ⟨G f t, ?_⟩
      have hm := G_mem hf ⟨ht, ht1⟩
      have : P (G f t) = G f t := by
        simp only [P]; rw [min_eq_left hm.2]; exact max_eq_right hm.1
      simp only [h, this, Ginv_G hf ⟨ht, ht1⟩]; ring
    · refine ⟨t - 1 + M, ?_⟩
      have : P (t - 1 + M) = M := by
        simp only [P]; rw [min_eq_right (by linarith)]; exact max_eq_right hM
      have hGt : Ginv f M = 1 := Ginv_top hf
      simp only [h, this, hGt]; ring
  have hcont : Continuous h := hmono.continuous_of_surjective hsurj
  refine hcont.continuousOn.congr ?_
  intro s hs
  have : P s = s := by simp only [P]; rw [min_eq_left hs.2]; exact max_eq_right hs.1
  simp [h, this]

/-! ### The bid function -/

section Bid
variable {f : ℝ → ℝ} (hf : Assumption1 f) {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1)
include hf hvl

lemma hvlI : vl ∈ Icc (0:ℝ) 1 := ⟨hvl.1.le, hvl.2.le⟩

lemma Gdiff_mem {v : ℝ} (hv : v ∈ Icc vl 1) : G f v - G f vl ∈ Icc 0 (G f 1) := by
  have h1 := (G_strictMonoOn hf).monotoneOn (hvlI hf hvl) ⟨hvl.1.le.trans hv.1, hv.2⟩ hv.1
  have h2 := G_mem hf ⟨hvl.1.le.trans hv.1, hv.2⟩
  have h3 := G_mem hf (hvlI hf hvl)
  constructor <;> linarith [h2.2, h3.1]

lemma bid_eq {v : ℝ} (hv : v ∈ Icc vl 1) : bidFn f vl v = Ginv f (G f v - G f vl) := by
  unfold bidFn
  split_ifs with h
  · have : v = vl := le_antisymm h hv.1
    subst this; simp [Ginv_zero hf]
  · rfl

lemma bid_of_le {v : ℝ} (hv : v ≤ vl) : bidFn f vl v = 0 := by
  unfold bidFn; simp [hv]

lemma bid_mem {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : bidFn f vl v ∈ Icc (0:ℝ) 1 := by
  rcases le_or_gt v vl with h | h
  · rw [bid_of_le hf hvl h]; exact ⟨le_rfl, zero_le_one⟩
  · rw [bid_eq hf hvl ⟨h.le, hv.2⟩]; exact Ginv_mem hf (Gdiff_mem hf hvl ⟨h.le, hv.2⟩)

lemma G_bid {v : ℝ} (hv : v ∈ Icc vl 1) : G f (bidFn f vl v) = G f v - G f vl := by
  rw [bid_eq hf hvl hv, G_Ginv hf (Gdiff_mem hf hvl hv)]

lemma bid_pos {v : ℝ} (hv : v ∈ Ioc vl 1) : 0 < bidFn f vl v := by
  have hm := bid_mem hf hvl (v := v) ⟨hvl.1.le.trans hv.1.le, hv.2⟩
  rcases hm.1.lt_or_eq with h | h
  · exact h
  · exfalso
    have := G_bid hf hvl ⟨hv.1.le, hv.2⟩
    rw [← h, G_zero] at this
    have := G_strictMonoOn hf (hvlI hf hvl) ⟨hvl.1.le.trans hv.1.le, hv.2⟩ hv.1
    linarith

lemma bid_lt {v : ℝ} (hv : v ∈ Ioc vl 1) : bidFn f vl v < v := by
  have hv' : v ∈ Icc (0:ℝ) 1 := ⟨hvl.1.le.trans hv.1.le, hv.2⟩
  by_contra hle
  push Not at hle
  have h1 := (G_strictMonoOn hf).monotoneOn hv' (bid_mem hf hvl hv') hle
  rw [G_bid hf hvl ⟨hv.1.le, hv.2⟩] at h1
  have := G_strictMonoOn hf ⟨le_rfl, zero_le_one⟩ (hvlI hf hvl) hvl.1
  rw [G_zero] at this
  linarith

lemma bid_le {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : bidFn f vl v ≤ v := by
  rcases le_or_gt v vl with h | h
  · rw [bid_of_le hf hvl h]; exact hv.1
  · exact (bid_lt hf hvl ⟨h, hv.2⟩).le

lemma bid_strictMonoOn : StrictMonoOn (bidFn f vl) (Icc vl 1) := by
  intro a ha b hb hab
  rw [bid_eq hf hvl ha, bid_eq hf hvl hb]
  apply Ginv_strictMonoOn hf (Gdiff_mem hf hvl ha) (Gdiff_mem hf hvl hb)
  have := G_strictMonoOn hf ⟨hvl.1.le.trans ha.1, ha.2⟩ ⟨hvl.1.le.trans hb.1, hb.2⟩ hab
  linarith

lemma bid_monotoneOn : MonotoneOn (bidFn f vl) (Icc 0 1) := by
  intro a ha b hb hab
  rcases le_or_gt a vl with h | h
  · rw [bid_of_le hf hvl h]; exact (bid_mem hf hvl hb).1
  · exact (bid_strictMonoOn hf hvl).monotoneOn ⟨h.le, ha.2⟩ ⟨h.le.trans hab, hb.2⟩ hab

lemma bid_contOn : ContinuousOn (bidFn f vl) (Icc 0 1) := by
  have hinner : ContinuousOn (fun v => max (G f v - G f vl) 0) (Icc 0 1) :=
    ContinuousOn.sup (f := fun v => G f v - G f vl) ((G_contOn hf).sub continuousOn_const)
      continuousOn_const
  have hmaps : MapsTo (fun v => max (G f v - G f vl) 0) (Icc 0 1) (Icc 0 (G f 1)) := by
    intro v hv
    have h2 := G_mem hf hv
    have h3 := G_mem hf (hvlI hf hvl)
    exact ⟨le_max_right _ _, max_le (by linarith [h2.2, h3.1]) (G_one_pos hf).le⟩
  refine ((Ginv_contOn hf).comp hinner hmaps).congr ?_
  intro v hv
  simp only [Function.comp]
  rcases le_or_gt v vl with h | h
  · rw [bid_of_le hf hvl h]
    have := (G_strictMonoOn hf).monotoneOn hv (hvlI hf hvl) h
    rw [max_eq_right (by linarith), Ginv_zero hf]
  · rw [bid_eq hf hvl ⟨h.le, hv.2⟩]
    have := (G_strictMonoOn hf).monotoneOn (hvlI hf hvl) hv h.le
    rw [max_eq_left (by linarith)]

/-- Derivative of the bid on `(vl, 1)` (inverse function theorem for `G`). -/
lemma bid_hasDerivAt {v : ℝ} (hv : v ∈ Ioo vl 1) :
    HasDerivAt (bidFn f vl) (v * f v / (bidFn f vl v * f (bidFn f vl v))) v := by
  set c := G f vl
  set M := G f 1
  have hv1 : v ∈ Icc (0:ℝ) 1 := ⟨hvl.1.le.trans hv.1.le, hv.2.le⟩
  set s0 := G f v - c with hs0
  have hcpos : 0 < c := by
    have := G_strictMonoOn hf ⟨le_rfl, zero_le_one⟩ (hvlI hf hvl) hvl.1
    rwa [G_zero] at this
  have hs0pos : 0 < s0 := by
    have := G_strictMonoOn hf (hvlI hf hvl) hv1 hv.1; simp only [hs0]; linarith
  have hs0lt : s0 < M := by
    have := G_strictMonoOn hf hv1 ⟨zero_le_one, le_rfl⟩ hv.2; simp only [hs0]; linarith
  set b := Ginv f s0 with hb
  have hbI : b ∈ Icc (0:ℝ) 1 := Ginv_mem hf ⟨hs0pos.le, hs0lt.le⟩
  have hGb : G f b = s0 := G_Ginv hf ⟨hs0pos.le, hs0lt.le⟩
  have hb0 : 0 < b := by
    rcases hbI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, G_zero] at hGb; linarith
  have hb1 : b < 1 := by
    rcases hbI.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hGb; linarith
  have hderG : HasDerivAt (G f) (b * f b) b := G_hasDerivAt hf ⟨hb0, hb1⟩
  have hne : b * f b ≠ 0 := (mul_pos hb0 (f_pos hf hbI)).ne'
  have hcont : ContinuousAt (Ginv f) s0 :=
    (Ginv_contOn hf).continuousAt (Icc_mem_nhds hs0pos hs0lt)
  have hev : ∀ᶠ y in 𝓝 s0, G f (Ginv f y) = y := by
    filter_upwards [Icc_mem_nhds hs0pos hs0lt] with y hy
    exact G_Ginv hf hy
  have hinv : HasDerivAt (Ginv f) (b * f b)⁻¹ s0 := HasDerivAt.of_local_left_inverse hcont hderG hne hev
  have hin : HasDerivAt (fun w => G f w - c) (v * f v) v :=
    (G_hasDerivAt hf ⟨hvl.1.trans hv.1, hv.2⟩).sub_const c
  have hcomp := hinv.comp v hin
  have heq : bidFn f vl v = b := by rw [bid_eq hf hvl ⟨hv.1.le, hv.2.le⟩]
  rw [heq]
  have : (b * f b)⁻¹ * (v * f v) = v * f v / (b * f b) := by field_simp
  rw [← this]
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
  simp only [Function.comp]
  exact bid_eq hf hvl ⟨hw.1.le, hw.2.le⟩

/-! ### The upper threshold `vh = b(1)` and the inverse bid `τ` -/

lemma vh_mem : bidFn f vl 1 ∈ Ioo (0:ℝ) 1 :=
  ⟨bid_pos hf hvl ⟨hvl.2, le_rfl⟩, bid_lt hf hvl ⟨hvl.2, le_rfl⟩⟩

lemma G_vh : G f (bidFn f vl 1) = G f 1 - G f vl := G_bid hf hvl ⟨hvl.2.le, le_rfl⟩

lemma Gsum_mem {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) :
    G f s + G f vl ∈ Icc (G f vl) (G f 1) := by
  have hvh := vh_mem hf hvl
  have h1 := G_mem hf ⟨hs.1, hs.2.trans hvh.2.le⟩
  have h2 := (G_strictMonoOn hf).monotoneOn ⟨hs.1, hs.2.trans hvh.2.le⟩ ⟨hvh.1.le, hvh.2.le⟩ hs.2
  rw [G_vh hf hvl] at h2
  constructor <;> linarith [h1.1]

lemma Gsum_mem' {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) :
    G f s + G f vl ∈ Icc 0 (G f 1) := by
  have := Gsum_mem hf hvl hs
  have h3 := G_mem hf (hvlI hf hvl)
  exact ⟨h3.1.trans this.1, this.2⟩

lemma inv_mem {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) : bidFnInv f vl s ∈ Icc vl 1 := by
  have h := Gsum_mem hf hvl hs
  have hm := Ginv_mem hf (Gsum_mem' hf hvl hs)
  refine ⟨?_, hm.2⟩
  by_contra hlt
  push Not at hlt
  have := G_strictMonoOn hf hm (hvlI hf hvl) hlt
  rw [G_Ginv hf (Gsum_mem' hf hvl hs)] at this
  linarith [h.1]

lemma G_inv {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) :
    G f (bidFnInv f vl s) = G f s + G f vl := G_Ginv hf (Gsum_mem' hf hvl hs)

lemma bid_inv {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) : bidFn f vl (bidFnInv f vl s) = s := by
  have hvh := vh_mem hf hvl
  rw [bid_eq hf hvl (inv_mem hf hvl hs), G_inv hf hvl hs]
  simp only [add_sub_cancel_right]
  exact Ginv_G hf ⟨hs.1, hs.2.trans hvh.2.le⟩

lemma inv_bid {v : ℝ} (hv : v ∈ Icc vl 1) : bidFnInv f vl (bidFn f vl v) = v := by
  unfold bidFnInv
  rw [G_bid hf hvl hv]
  simp only [sub_add_cancel]
  exact Ginv_G hf ⟨hvl.1.le.trans hv.1, hv.2⟩

lemma bid_mem_vh {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : bidFn f vl v ∈ Icc 0 (bidFn f vl 1) :=
  ⟨(bid_mem hf hvl hv).1, bid_monotoneOn hf hvl hv ⟨zero_le_one, le_rfl⟩ hv.2⟩

lemma inv_strictMonoOn : StrictMonoOn (bidFnInv f vl) (Icc 0 (bidFn f vl 1)) := by
  intro a ha b hb hab
  have hvh := vh_mem hf hvl
  unfold bidFnInv
  apply Ginv_strictMonoOn hf (Gsum_mem' hf hvl ha) (Gsum_mem' hf hvl hb)
  have := G_strictMonoOn hf ⟨ha.1, ha.2.trans hvh.2.le⟩ ⟨hb.1, hb.2.trans hvh.2.le⟩ hab
  linarith

lemma inv_contOn : ContinuousOn (bidFnInv f vl) (Icc 0 (bidFn f vl 1)) := by
  have hvh := vh_mem hf hvl
  have hinner : ContinuousOn (fun s => G f s + G f vl) (Icc 0 (bidFn f vl 1)) :=
    ((G_contOn hf).mono (Icc_subset_Icc le_rfl hvh.2.le)).add continuousOn_const
  exact (Ginv_contOn hf).comp hinner (fun s hs => Gsum_mem' hf hvl hs)

lemma inv_zero : bidFnInv f vl 0 = vl := by
  unfold bidFnInv; rw [G_zero, zero_add, Ginv_G hf (hvlI hf hvl)]

lemma inv_vh : bidFnInv f vl (bidFn f vl 1) = 1 := inv_bid hf hvl ⟨hvl.2.le, le_rfl⟩

lemma inv_pos {s : ℝ} (hs : s ∈ Icc 0 (bidFn f vl 1)) : 0 < bidFnInv f vl s :=
  hvl.1.trans_le (inv_mem hf hvl hs).1

end Bid

end DIThm2

theorem solution (f : ℝ → ℝ) (hf : DeferredInspection.SingleAgent.Assumption1 f)
    (vl : ℝ) (hvl : vl ∈ Ioo (0 : ℝ) 1) :
    ∀ v ∈ Ioo vl 1,
      DifferentiableAt ℝ (DeferredInspection.SingleAgent.bidFn f vl) v ∧
      f v * v = DeferredInspection.SingleAgent.bidFn f vl v *
        f (DeferredInspection.SingleAgent.bidFn f vl v) *
        deriv (DeferredInspection.SingleAgent.bidFn f vl) v := by
  intro v hv
  have hd := DIThm2.bid_hasDerivAt hf hvl hv
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hb := DIThm2.bid_pos hf hvl ⟨hv.1, hv.2.le⟩
  have hbI := DIThm2.bid_mem hf hvl (v := v) ⟨hvl.1.le.trans hv.1.le, hv.2.le⟩
  have hne : bidFn f vl v * f (bidFn f vl v) ≠ 0 := (mul_pos hb (DIThm2.f_pos hf hbI)).ne'
  rw [mul_div_cancel₀ _ hne, mul_comm]
