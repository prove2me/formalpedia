-- Prove2me | solution 1 for DeferredInspection.SingleAgent.eq_15_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:16:19.461175+00:00
-- url     : https://prove2.me/submissions/420e9c10-ab0c-4dac-be2d-def16e2adf54

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

/-- Derivative of the bid, as a function. -/
noncomputable def dbid (f : ℝ → ℝ) (vl v : ℝ) : ℝ :=
  v * f v / (bidFn f vl v * f (bidFn f vl v))

lemma dbid_pos {v : ℝ} (hv : v ∈ Ioc vl 1) : 0 < dbid f vl v := by
  have hv1 : v ∈ Icc (0:ℝ) 1 := ⟨hvl.1.le.trans hv.1.le, hv.2⟩
  have hb := bid_pos hf hvl hv
  have hbI := bid_mem hf hvl hv1
  unfold dbid
  exact div_pos (mul_pos (hvl.1.trans hv.1) (f_pos hf hv1)) (mul_pos hb (f_pos hf hbI))

lemma image_bid {a : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) :
    bidFn f vl '' Ioo vl (bidFnInv f vl a) = Ioo 0 a := by
  have hτa := inv_mem hf hvl ha
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨bid_pos hf hvl ⟨ht.1, ht.2.le.trans hτa.2⟩, ?_⟩
    have := bid_strictMonoOn hf hvl ⟨ht.1.le, ht.2.le.trans hτa.2⟩ hτa ht.2
    rwa [bid_inv hf hvl ha] at this
  · intro hs
    have hsI : s ∈ Icc 0 (bidFn f vl 1) := ⟨hs.1.le, hs.2.le.trans ha.2⟩
    refine ⟨bidFnInv f vl s, ⟨?_, ?_⟩, bid_inv hf hvl hsI⟩
    · have := inv_strictMonoOn hf hvl ⟨le_rfl, (vh_mem hf hvl).1.le⟩ hsI hs.1
      rwa [inv_zero hf hvl] at this
    · exact inv_strictMonoOn hf hvl hsI ha hs.2

/-- Change of variables `u = b(t)` on `(vl, b⁻¹(a))`. -/
lemma change_var {a : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) (g : ℝ → ℝ) :
    ∫ u in Ioo 0 a, g u = ∫ t in Ioo vl (bidFnInv f vl a), dbid f vl t * g (bidFn f vl t) := by
  have hτa := inv_mem hf hvl ha
  rw [← image_bid hf hvl ha]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo (f' := dbid f vl)]
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only [smul_eq_mul]
    rw [abs_of_pos (dbid_pos hf hvl ⟨ht.1, ht.2.le.trans hτa.2⟩)]
  · intro t ht
    have : t ∈ Ioo vl 1 := ⟨ht.1, ht.2.trans_le hτa.2⟩
    exact (bid_hasDerivAt hf hvl this).hasDerivWithinAt
  · refine (bid_strictMonoOn hf hvl).injOn.mono ?_
    intro t ht; exact ⟨ht.1.le, ht.2.le.trans hτa.2⟩

lemma change_var_int {a : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) (g : ℝ → ℝ) :
    IntegrableOn g (Ioo 0 a) ↔
      IntegrableOn (fun t => dbid f vl t * g (bidFn f vl t)) (Ioo vl (bidFnInv f vl a)) := by
  have hτa := inv_mem hf hvl ha
  rw [← image_bid hf hvl ha]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo (f' := dbid f vl)]
  · apply integrableOn_congr_fun _ measurableSet_Ioo
    intro t ht
    simp only [smul_eq_mul]
    rw [abs_of_pos (dbid_pos hf hvl ⟨ht.1, ht.2.le.trans hτa.2⟩)]
  · intro t ht
    have : t ∈ Ioo vl 1 := ⟨ht.1, ht.2.trans_le hτa.2⟩
    exact (bid_hasDerivAt hf hvl this).hasDerivWithinAt
  · refine (bid_strictMonoOn hf hvl).injOn.mono ?_
    intro t ht; exact ⟨ht.1.le, ht.2.le.trans hτa.2⟩

lemma deriv_bid {t : ℝ} (ht : t ∈ Ioo vl 1) : deriv (bidFn f vl) t = dbid f vl t :=
  (bid_hasDerivAt hf hvl ht).deriv

/-- The allocation integral in terms of `τ = b⁻¹`. -/
lemma alloc_integral {a : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) :
    ∫ t in vl..bidFnInv f vl a, deriv (bidFn f vl) t / t =
      ∫ s in (0:ℝ)..a, (bidFnInv f vl s)⁻¹ := by
  have hτa := inv_mem hf hvl ha
  rw [intervalIntegral.integral_of_le hτa.1, intervalIntegral.integral_of_le ha.1,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, change_var hf hvl ha]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Ioo vl 1 := ⟨ht.1, ht.2.trans_le hτa.2⟩
  simp only
  rw [deriv_bid hf hvl ht', inv_bid hf hvl ⟨ht.1.le, ht'.2.le⟩, div_eq_mul_inv]

lemma invinv_contOn : ContinuousOn (fun s => (bidFnInv f vl s)⁻¹) (Icc 0 (bidFn f vl 1)) :=
  (inv_contOn hf hvl).inv₀ (fun s hs => (inv_pos hf hvl hs).ne')

lemma invinv_ii {a b : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) (hb : b ∈ Icc 0 (bidFn f vl 1)) :
    IntervalIntegrable (fun s => (bidFnInv f vl s)⁻¹) volume a b :=
  ((invinv_contOn hf hvl).mono (uIcc_subset_Icc ha hb)).intervalIntegrable

end Bid

/-! ### The allocation in `τ`-form and feasibility of Theorem 2's mechanism -/

/-- `X(w) = ∫_0^{min w vh} 1/τ`. -/
noncomputable def Xf (f : ℝ → ℝ) (vl w : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..min w (bidFn f vl 1), (bidFnInv f vl s)⁻¹

section Mech
variable {f : ℝ → ℝ} (hf : Assumption1 f) {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1)
include hf hvl

lemma min_mem {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : min w (bidFn f vl 1) ∈ Icc 0 (bidFn f vl 1) :=
  ⟨le_min hw.1 (vh_mem hf hvl).1.le, min_le_right _ _⟩

lemma X_bid {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    Xf f vl (bidFn f vl v) = ∫ s in (0:ℝ)..bidFn f vl v, (bidFnInv f vl s)⁻¹ := by
  unfold Xf; rw [min_eq_left (bid_mem_vh hf hvl hv).2]

lemma X_zero : Xf f vl 0 = 0 := by
  unfold Xf; rw [min_eq_left (vh_mem hf hvl).1.le]; simp

lemma F_sub {a b : ℝ} (ha : a ∈ Icc 0 (bidFn f vl 1)) (hb : b ∈ Icc 0 (bidFn f vl 1)) :
    (∫ s in (0:ℝ)..b, (bidFnInv f vl s)⁻¹) - (∫ s in (0:ℝ)..a, (bidFnInv f vl s)⁻¹) =
      ∫ s in a..b, (bidFnInv f vl s)⁻¹ := by
  have h0 : (0:ℝ) ∈ Icc 0 (bidFn f vl 1) := ⟨le_rfl, (vh_mem hf hvl).1.le⟩
  exact intervalIntegral.integral_interval_sub_left (invinv_ii hf hvl h0 hb) (invinv_ii hf hvl h0 ha)

lemma X_IC {v w : ℝ} (hv : v ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    v * Xf f vl w - w ≤ v * Xf f vl (bidFn f vl v) - bidFn f vl v := by
  set vh := bidFn f vl 1 with hvhdef
  set a := bidFn f vl v with hadef
  have haI : a ∈ Icc 0 vh := bid_mem_vh hf hvl hv
  have hXa := X_bid hf hvl hv
  rw [← hadef] at hXa
  rw [hXa]
  set m := min w vh with hmdef
  have hmI : m ∈ Icc 0 vh := min_mem hf hvl hw
  have hXw : Xf f vl w = ∫ s in (0:ℝ)..m, (bidFnInv f vl s)⁻¹ := rfl
  rw [hXw]
  rcases le_or_gt a m with ham | hma
  · -- `τ ≥ v` on `[a, m]`
    have hge : ∀ s ∈ Icc a m, v ≤ bidFnInv f vl s := by
      intro s hs
      have hsI : s ∈ Icc 0 vh := ⟨haI.1.trans hs.1, hs.2.trans hmI.2⟩
      rcases le_or_gt v vl with hvv | hvv
      · exact hvv.trans (inv_mem hf hvl hsI).1
      · have := (inv_strictMonoOn hf hvl).monotoneOn haI hsI hs.1
        rwa [hadef, inv_bid hf hvl ⟨hvv.le, hv.2⟩] at this
    have hdiff := F_sub hf hvl haI hmI
    have hbound : v * ∫ s in a..m, (bidFnInv f vl s)⁻¹ ≤ m - a := by
      rw [← intervalIntegral.integral_const_mul]
      have := intervalIntegral.integral_mono_on ham
        ((invinv_ii hf hvl haI hmI).const_mul v) (intervalIntegrable_const (c := (1:ℝ)))
        (fun s hs => by
          have hpos := inv_pos hf hvl ⟨haI.1.trans hs.1, hs.2.trans hmI.2⟩
          rw [← div_eq_mul_inv, div_le_one hpos]; exact hge s hs)
      simpa using this
    have hmw : m ≤ w := min_le_left _ _
    have e := congrArg (fun z => v * z) hdiff
    simp only [mul_sub] at e
    linarith
  · have hmw : m = w := by
      rcases le_total w vh with h | h
      · exact min_eq_left h
      · exfalso; have : m = vh := min_eq_right h; linarith [haI.2]
    rw [hmw] at hma hmI ⊢
    have hapos : 0 < a := hmI.1.trans_lt hma
    have hvv : vl < v := by
      by_contra h; push Not at h
      have : a = 0 := bid_of_le hf hvl h
      linarith
    have hle : ∀ s ∈ Icc w a, bidFnInv f vl s ≤ v := by
      intro s hs
      have hsI : s ∈ Icc 0 vh := ⟨hmI.1.trans hs.1, hs.2.trans haI.2⟩
      have := (inv_strictMonoOn hf hvl).monotoneOn hsI haI hs.2
      rwa [hadef, inv_bid hf hvl ⟨hvv.le, hv.2⟩] at this
    have hdiff := F_sub hf hvl hmI haI
    have hbound : a - w ≤ v * ∫ s in w..a, (bidFnInv f vl s)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      have := intervalIntegral.integral_mono_on hma.le (intervalIntegrable_const (c := (1:ℝ)))
        ((invinv_ii hf hvl hmI haI).const_mul v)
        (fun s hs => by
          have hpos := inv_pos hf hvl ⟨hmI.1.trans hs.1, hs.2.trans haI.2⟩
          rw [← div_eq_mul_inv, one_le_div hpos]; exact hle s hs)
      simpa using this
    have e := congrArg (fun z => v * z) hdiff
    simp only [mul_sub] at e
    linarith

variable (hB : ∫ s in (0:ℝ)..bidFn f vl 1, (bidFnInv f vl s)⁻¹ = 1)
include hB

lemma X_of_ge {w : ℝ} (hw : bidFn f vl 1 ≤ w) : Xf f vl w = 1 := by
  unfold Xf; rw [min_eq_right hw, hB]

lemma X_mem {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : Xf f vl w ∈ Icc (0:ℝ) 1 := by
  have hmI := min_mem hf hvl hw
  have hvhI : bidFn f vl 1 ∈ Icc 0 (bidFn f vl 1) := ⟨(vh_mem hf hvl).1.le, le_rfl⟩
  have hnn : ∀ a ∈ Icc 0 (bidFn f vl 1), ∀ b ∈ Icc 0 (bidFn f vl 1), a ≤ b →
      0 ≤ ∫ s in a..b, (bidFnInv f vl s)⁻¹ := by
    intro a ha b hb hab
    apply intervalIntegral.integral_nonneg_of_forall hab
    intro s
    exact inv_nonneg.2 (by
      unfold bidFnInv
      by_cases hs : G f s + G f vl ∈ Icc 0 (G f 1)
      · exact (Ginv_mem hf hs).1
      · unfold Ginv
        apply Real.sInf_nonneg
        intro y hy; exact hy.1.1)
  have h0 : (0:ℝ) ∈ Icc 0 (bidFn f vl 1) := ⟨le_rfl, (vh_mem hf hvl).1.le⟩
  constructor
  · exact hnn 0 h0 _ hmI hmI.1
  · have := F_sub hf hvl hmI hvhI
    have h2 := hnn _ hmI _ hvhI hmI.2
    unfold Xf; linarith

lemma alloc_eq_X {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) :
    optAlloc f vl (bidFn f vl 1) w = Xf f vl w := by
  unfold optAlloc
  split_ifs with h
  · rw [X_of_ge hf hvl hB h]
  · push Not at h
    unfold Xf
    rw [min_eq_left h.le]
    exact alloc_integral hf hvl ⟨hw.1, h.le⟩

lemma X_contOn : ContinuousOn (Xf f vl) (Icc 0 1) := by
  have hvh := vh_mem hf hvl
  have hprim := intervalIntegral.continuousOn_primitive_interval' (a := 0)
    (invinv_ii hf hvl (a := 0) (b := bidFn f vl 1) ⟨le_rfl, hvh.1.le⟩ ⟨hvh.1.le, le_rfl⟩)
    (by rw [uIcc_of_le hvh.1.le]; exact ⟨le_rfl, hvh.1.le⟩)
  rw [uIcc_of_le hvh.1.le] at hprim
  have hmin : ContinuousOn (fun w => min w (bidFn f vl 1)) (Icc 0 1) :=
    (continuous_id.min continuous_const).continuousOn
  exact hprim.comp hmin (fun w hw => min_mem hf hvl hw)

lemma pay_eq {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    optPayment f vl (bidFn f vl 1) v =
      v * (Xf f vl v - Xf f vl (bidFn f vl v)) + bidFn f vl v := by
  have hbI := bid_mem hf hvl hv
  unfold optPayment
  split_ifs with h1 h2
  · rw [bid_of_le hf hvl h1, X_zero hf hvl, alloc_eq_X hf hvl hB hv]; ring
  · rw [alloc_eq_X hf hvl hB hv, alloc_eq_X hf hvl hB hbI]
  · push Not at h2
    rw [alloc_eq_X hf hvl hB hbI, X_of_ge hf hvl hB h2]

lemma mech_feasible :
    IsFeasible f (optAlloc f vl (bidFn f vl 1)) (optPayment f vl (bidFn f vl 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [alloc_eq_X hf hvl hB hv]; exact X_mem hf hvl hB hv
  · intro v hv w hw
    rw [alloc_eq_X hf hvl hB hv, alloc_eq_X hf hvl hB hw, pay_eq hf hvl hB hv]
    have := X_IC hf hvl hv hw
    linarith
  · intro v hv
    rw [alloc_eq_X hf hvl hB hv, pay_eq hf hvl hB hv]
    have := X_IC hf hvl hv (w := 0) ⟨le_rfl, zero_le_one⟩
    rw [X_zero hf hvl] at this
    linarith
  · apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hq : ContinuousOn (fun v => (v * (Xf f vl v - Xf f vl (bidFn f vl v)) + bidFn f vl v) * f v)
        (Icc 0 1) := by
      have h1 := X_contOn hf hvl hB
      have h2 : ContinuousOn (fun v => Xf f vl (bidFn f vl v)) (Icc 0 1) :=
        h1.comp (bid_contOn hf hvl) (fun v hv => bid_mem hf hvl hv)
      exact ((continuousOn_id.mul (h1.sub h2)).add (bid_contOn hf hvl)).mul (f_contOn hf)
    refine hq.congr ?_
    intro v hv
    simp only
    rw [pay_eq hf hvl hB hv]

end Mech

/-! ### The revenue identity -/

section Rev
variable {f : ℝ → ℝ} (hf : Assumption1 f) {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1)
include hf hvl

lemma dbid_mul {t : ℝ} (ht : t ∈ Ioc vl 1) :
    dbid f vl t * (bidFn f vl t * f (bidFn f vl t)) = t * f t := by
  have hb := bid_pos hf hvl ht
  have hbI := bid_mem hf hvl (v := t) ⟨hvl.1.le.trans ht.1.le, ht.2⟩
  have hne : bidFn f vl t * f (bidFn f vl t) ≠ 0 := (mul_pos hb (f_pos hf hbI)).ne'
  unfold dbid
  rw [div_mul_cancel₀ _ hne]

lemma rev_identity (y : ℝ → ℝ) (hy : IntegrableOn y (Icc 0 1)) :
    IntervalIntegrable (fun v => (v * y v - v * y (bidFn f vl v) + bidFn f vl v) * f v)
        volume 0 1 ∧
    ∫ v in (0:ℝ)..1, (v * y v - v * y (bidFn f vl v) + bidFn f vl v) * f v =
      (∫ v in bidFn f vl 1..1, v * f v * y v) - y 0 * (∫ v in (0:ℝ)..vl, v * f v) +
        ∫ v in (0:ℝ)..1, bidFn f vl v * f v := by
  set vh := bidFn f vl 1 with hvhdef
  have hvh := vh_mem hf hvl
  have hvhI : vh ∈ Icc 0 vh := ⟨hvh.1.le, le_rfl⟩
  -- integrability of `w y`
  have h1 : IntegrableOn (fun v => v * f v * y v) (Icc 0 1) :=
    hy.continuousOn_mul (yf_contOn hf) isCompact_Icc
  have h1' : IntervalIntegrable (fun v => v * f v * y v) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 h1
  -- the change of variables on `(vl, 1)`
  have hcv := change_var hf hvl hvhI (fun u => u * f u * y u)
  have hcvi := change_var_int hf hvl hvhI (fun u => u * f u * y u)
  rw [inv_vh hf hvl] at hcv hcvi
  have hEq : EqOn (fun t => dbid f vl t * (bidFn f vl t * f (bidFn f vl t) * y (bidFn f vl t)))
      (fun t => t * f t * y (bidFn f vl t)) (Ioo vl 1) := by
    intro t ht
    simp only
    rw [← mul_assoc, dbid_mul hf hvl ⟨ht.1, ht.2.le⟩]
  rw [setIntegral_congr_fun measurableSet_Ioo hEq] at hcv
  have hint0 : IntegrableOn (fun u => u * f u * y u) (Ioo 0 vh) :=
    h1.mono_set (fun u hu => ⟨hu.1.le, hu.2.le.trans hvh.2.le⟩)
  have hint1 : IntegrableOn (fun t => t * f t * y (bidFn f vl t)) (Ioo vl 1) :=
    (hcvi.1 hint0).congr_fun hEq measurableSet_Ioo
  have hii1 : IntervalIntegrable (fun t => t * f t * y (bidFn f vl t)) volume vl 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hvl.2.le).2 hint1
  have hcvI : ∫ t in vl..1, t * f t * y (bidFn f vl t) = ∫ u in (0:ℝ)..vh, u * f u * y u := by
    rw [intervalIntegral.integral_of_le hvl.2.le, intervalIntegral.integral_of_le hvh.1.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, hcv]
  -- the piece on `[0, vl]`
  have hEq0 : EqOn (fun t => t * f t * y (bidFn f vl t)) (fun t => t * f t * y 0) (uIcc 0 vl) := by
    intro t ht
    rw [uIcc_of_le hvl.1.le] at ht
    simp only [bid_of_le hf hvl ht.2]
  have hvlI : vl ∈ Icc (0:ℝ) 1 := hvlI hf hvl
  have hii0 : IntervalIntegrable (fun t => t * f t * y (bidFn f vl t)) volume 0 vl := by
    have : IntervalIntegrable (fun t => t * f t * y 0) volume 0 vl :=
      (yf_ii hf ⟨le_rfl, zero_le_one⟩ hvlI).mul_const _
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hvl.1.le] at this ⊢
    refine this.congr_fun ?_ measurableSet_Icc
    intro t ht; exact (hEq0 (by rw [uIcc_of_le hvl.1.le]; exact ht)).symm
  have hI0 : ∫ t in (0:ℝ)..vl, t * f t * y (bidFn f vl t) = y 0 * ∫ t in (0:ℝ)..vl, t * f t := by
    rw [intervalIntegral.integral_congr hEq0, intervalIntegral.integral_mul_const, mul_comm]
  have hii2 : IntervalIntegrable (fun t => t * f t * y (bidFn f vl t)) volume 0 1 :=
    hii0.trans hii1
  have hii3 : IntervalIntegrable (fun t => bidFn f vl t * f t) volume 0 1 :=
    ((bid_contOn hf hvl).mul (f_contOn hf)).intervalIntegrable_of_Icc zero_le_one
  have hfun : (fun v => (v * y v - v * y (bidFn f vl v) + bidFn f vl v) * f v) =
      fun v => v * f v * y v - v * f v * y (bidFn f vl v) + bidFn f vl v * f v := by
    funext v; ring
  rw [hfun]
  refine ⟨(h1'.sub hii2).add hii3, ?_⟩
  rw [intervalIntegral.integral_add (h1'.sub hii2) hii3,
    intervalIntegral.integral_sub h1' hii2]
  rw [← intervalIntegral.integral_add_adjacent_intervals hii0 hii1, hI0, hcvI]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := vh) (c := 1)
    (h1'.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hvh.1.le]; exact Icc_subset_Icc le_rfl hvh.2.le))
    (h1'.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hvh.2.le]; exact Icc_subset_Icc hvh.1.le le_rfl))
  rw [← hsplit]
  ring

end Rev

/-! ### The concave envelope of an arbitrary feasible allocation -/

/-- `φ(q) = sup_{w ∈ [0,1]} (q x(w) - w)`. -/
noncomputable def phiE (x : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup ((fun w => q * x w - w) '' Icc 0 1)

/-- `y(u) = inf_{q > 0} (φ(q) + u⁺)/q`, a monotone majorant of `x` with the same `φ`. -/
noncomputable def yE (x : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf ((fun q => (phiE x q + max u 0) / q) '' Ioi 0)

section Env
variable {x : ℝ → ℝ} (hx : IsAllocation x)
include hx

lemma phi_bdd {q : ℝ} (hq : 0 ≤ q) : BddAbove ((fun w => q * x w - w) '' Icc 0 1) := by
  refine ⟨q, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have := hx w hw
  nlinarith [this.2, hw.1]

lemma phi_ge {q : ℝ} (hq : 0 ≤ q) {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : q * x w - w ≤ phiE x q :=
  le_csSup (phi_bdd hx hq) ⟨w, hw, rfl⟩

lemma phi_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ phiE x q := by
  have := phi_ge hx hq (w := 0) ⟨le_rfl, zero_le_one⟩
  have h0 := (hx 0 ⟨le_rfl, zero_le_one⟩).1
  nlinarith

lemma phi_le {q : ℝ} (hq : 0 ≤ q) : phiE x q ≤ q := by
  apply csSup_le ((nonempty_Icc.2 zero_le_one).image _)
  rintro _ ⟨w, hw, rfl⟩
  have := hx w hw
  nlinarith [this.2, hw.1]

lemma yset_bdd (u : ℝ) : BddBelow ((fun q => (phiE x q + max u 0) / q) '' Ioi 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact div_nonneg (add_nonneg (phi_nonneg hx (le_of_lt hq)) (le_max_right _ _)) (le_of_lt hq)

lemma y_le {q : ℝ} (hq : 0 < q) (u : ℝ) : yE x u ≤ (phiE x q + max u 0) / q :=
  csInf_le (yset_bdd hx u) ⟨q, hq, rfl⟩

lemma y_mono : Monotone (yE x) := by
  intro u u' huu
  apply le_csInf (nonempty_Ioi.image _)
  rintro _ ⟨q, hq, rfl⟩
  refine (y_le hx hq u).trans ?_
  exact div_le_div_of_nonneg_right (by linarith [max_le_max huu (le_refl (0:ℝ))]) (le_of_lt hq)

lemma y_ge_x {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : x u ≤ yE x u := by
  apply le_csInf (nonempty_Ioi.image _)
  rintro _ ⟨q, hq, rfl⟩
  simp only [max_eq_left hu.1]
  rw [le_div_iff₀ hq]
  have := phi_ge hx (le_of_lt hq) hu
  linarith

lemma y_nonneg {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : 0 ≤ yE x u :=
  (hx u hu).1.trans (y_ge_x hx hu)

lemma y_le_one {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : yE x u ≤ 1 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hq : 0 < (u + 1) / ε := div_pos (by linarith [hu.1]) hε
  refine (y_le hx hq u).trans ?_
  rw [max_eq_left hu.1, div_le_iff₀ hq]
  have := phi_le hx (le_of_lt hq)
  have h2 : (1 + ε) * ((u + 1) / ε) = (u + 1) / ε + (u + 1) := by field_simp
  rw [h2]
  linarith

lemma y_conj {q : ℝ} (hq : 0 < q) {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : q * yE x w - w ≤ phiE x q := by
  have := y_le hx hq w
  rw [max_eq_left hw.1, le_div_iff₀ hq] at this
  linarith

lemma y_integrable : IntegrableOn (yE x) (Icc 0 1) :=
  (y_mono hx).monotoneOn _ |>.integrableOn_isCompact isCompact_Icc

end Env

section Opt
variable {f : ℝ → ℝ} (hf : Assumption1 f) {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1)
include hf hvl

lemma pointwise_bound {x p : ℝ → ℝ} (hfe : IsFeasible f x p) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    p v ≤ v * yE x v - v * yE x (bidFn f vl v) + bidFn f vl v := by
  obtain ⟨hx, hIC, hIR, -⟩ := hfe
  rcases hv.1.lt_or_eq with hv0 | hv0
  · have hphi : phiE x v ≤ v * x v - p v := by
      apply csSup_le ((nonempty_Icc.2 zero_le_one).image _)
      rintro _ ⟨w, hw, rfl⟩
      exact hIC v hv w hw
    have h1 := y_ge_x hx hv
    have h2 := y_conj hx hv0 (bid_mem hf hvl hv)
    nlinarith
  · subst hv0
    have := hIR 0 hv
    rw [bid_of_le hf hvl hvl.1.le]
    simp only [zero_mul] at this ⊢
    linarith

lemma optimal_of_bc (hB : ∫ s in (0:ℝ)..bidFn f vl 1, (bidFnInv f vl s)⁻¹ = 1) :
    IsOptimal f (optAlloc f vl (bidFn f vl 1)) (optPayment f vl (bidFn f vl 1)) := by
  set vh := bidFn f vl 1 with hvhdef
  have hvh := vh_mem hf hvl
  refine ⟨mech_feasible hf hvl hB, ?_⟩
  intro x' p' hfe
  -- value of the optimal mechanism
  have hXint : IntegrableOn (Xf f vl) (Icc 0 1) :=
    (X_contOn hf hvl hB).integrableOn_compact isCompact_Icc
  obtain ⟨-, hrevX⟩ := rev_identity hf hvl (Xf f vl) hXint
  have hrev_opt : revenue f (optPayment f vl vh) =
      ∫ v in (0:ℝ)..1, (v * Xf f vl v - v * Xf f vl (bidFn f vl v) + bidFn f vl v) * f v := by
    unfold revenue
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    simp only
    rw [pay_eq hf hvl hB hv]; ring
  have hX1 : ∫ v in vh..1, v * f v * Xf f vl v = ∫ v in vh..1, v * f v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hvh.2.le] at hv
    simp only
    rw [X_of_ge hf hvl hB hv.1, mul_one]
  rw [hX1, X_zero hf hvl, zero_mul, sub_zero] at hrevX
  rw [hrev_opt, hrevX]
  -- upper bound for an arbitrary feasible mechanism
  have hx' := hfe.1
  have hyint := y_integrable hx'
  obtain ⟨hii, hrevY⟩ := rev_identity hf hvl (yE x') hyint
  have hle1 : revenue f p' ≤
      ∫ v in (0:ℝ)..1, (v * yE x' v - v * yE x' (bidFn f vl v) + bidFn f vl v) * f v := by
    unfold revenue
    apply intervalIntegral.integral_mono_on zero_le_one hfe.2.2.2 hii
    intro v hv
    exact mul_le_mul_of_nonneg_right (pointwise_bound hf hvl hfe hv) (f_pos hf hv).le
  rw [hrevY] at hle1
  have hvhI : vh ∈ Icc (0:ℝ) 1 := ⟨hvh.1.le, hvh.2.le⟩
  have hle2 : ∫ v in vh..1, v * f v * yE x' v ≤ ∫ v in vh..1, v * f v := by
    apply intervalIntegral.integral_mono_on hvh.2.le
    · have h1 : IntegrableOn (fun v => v * f v * yE x' v) (Icc 0 1) :=
        hyint.continuousOn_mul (yf_contOn hf) isCompact_Icc
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hvh.2.le]
      exact h1.mono_set (Icc_subset_Icc hvh.1.le le_rfl)
    · exact yf_ii hf hvhI ⟨zero_le_one, le_rfl⟩
    · intro v hv
      have hvI : v ∈ Icc (0:ℝ) 1 := ⟨hvh.1.le.trans hv.1, hv.2⟩
      have hw : 0 ≤ v * f v := mul_nonneg hvI.1 (f_pos hf hvI).le
      have := y_le_one hx' hvI
      nlinarith
  have hle3 : 0 ≤ yE x' 0 * ∫ v in (0:ℝ)..vl, v * f v := by
    apply mul_nonneg (y_nonneg hx' ⟨le_rfl, zero_le_one⟩)
    apply intervalIntegral.integral_nonneg hvl.1.le
    intro v hv
    exact mul_nonneg hv.1 (f_pos hf ⟨hv.1, hv.2.trans hvl.2.le⟩).le
  linarith

end Opt

/-! ### Boundary conditions force `vl ∈ (0,1)` -/

lemma bc_vl {f : ℝ → ℝ} (hf : Assumption1 f) {vl vh : ℝ} (h : BoundaryConds f vl vh) :
    vl ∈ Ioo (0:ℝ) 1 := by
  obtain ⟨hvlI, hvh, hint⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hvlI.1.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      subst h0
      have hb : ∀ t ∈ Ioc (0:ℝ) 1, bidFn f 0 t = t := by
        intro t ht
        unfold bidFn
        rw [if_neg (not_le.2 ht.1), G_zero, sub_zero, Ginv_G hf ⟨ht.1.le, ht.2⟩]
      have hvh1 : vh = 1 := by rw [hvh, hb 1 ⟨zero_lt_one, le_rfl⟩]
      have hinv1 : bidFnInv f 0 vh = 1 := by
        rw [hvh1]; unfold bidFnInv; rw [G_zero, add_zero, Ginv_top hf]
      rw [hinv1] at hint
      have hcongr : ∫ t in (0:ℝ)..1, deriv (bidFn f 0) t / t = ∫ t in (0:ℝ)..1, t⁻¹ := by
        rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
          integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hev : bidFn f 0 =ᶠ[𝓝 t] id := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
          exact hb u ⟨hu.1, hu.2.le⟩
        simp only
        rw [hev.deriv_eq, deriv_id, one_div]
      rw [hcongr, intervalIntegral.integral_undef (by simp)] at hint
      norm_num at hint
  · rcases hvlI.2.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      subst h1
      have hvh0 : vh = 0 := by rw [hvh]; unfold bidFn; simp
      rw [hvh0] at hint
      have : bidFnInv f 1 0 = 1 := by
        unfold bidFnInv; rw [G_zero, zero_add, Ginv_top hf]
      rw [this] at hint
      simp at hint

/-! ### Existence of the thresholds -/

section Exist
variable {f : ℝ → ℝ} (hf : Assumption1 f)
include hf

/-- The threshold function `H(vl) = ∫_0^{b(1)} 1/τ`. -/
noncomputable def Hfun (f : ℝ → ℝ) (vl : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..bidFn f vl 1, (bidFnInv f vl s)⁻¹

omit hf in
lemma clamp_cont (lo hi : ℝ) : Continuous (fun t : ℝ => max lo (min t hi)) :=
  continuous_const.max (continuous_id.min continuous_const)

omit hf in
lemma clamp_mem {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) : max lo (min t hi) ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

omit hf in
lemma clamp_eq {lo hi t : ℝ} (ht : t ∈ Icc lo hi) : max lo (min t hi) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

lemma Gc_cont : Continuous (fun t => G f (max 0 (min t 1))) :=
  (G_contOn hf).comp_continuous (clamp_cont 0 1) (clamp_mem zero_le_one)

lemma Gi_cont : Continuous (fun s => Ginv f (max 0 (min s (G f 1)))) :=
  (Ginv_contOn hf).comp_continuous (clamp_cont 0 _) (clamp_mem (G_one_pos hf).le)

lemma H_le_of {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) (hbb : bidFn f b 1 ≤ b) : Hfun f b ≤ 1 := by
  have hvh := vh_mem hf hb
  unfold Hfun
  have h1 : ∫ s in (0:ℝ)..bidFn f b 1, (bidFnInv f b s)⁻¹ ≤ ∫ s in (0:ℝ)..bidFn f b 1, b⁻¹ := by
    apply intervalIntegral.integral_mono_on hvh.1.le
      (invinv_ii hf hb ⟨le_rfl, hvh.1.le⟩ ⟨hvh.1.le, le_rfl⟩) intervalIntegrable_const
    intro s hs
    exact inv_anti₀ hb.1 (inv_mem hf hb hs).1
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← div_eq_mul_inv] at h1
  have : bidFn f b 1 / b ≤ 1 := (div_le_one hb.1).2 hbb
  linarith

lemma exists_b : ∃ b ∈ Ioo (0:ℝ) 1, bidFn f b 1 ≤ b := by
  set M := G f 1
  have hM := G_one_pos hf
  have h3 : 3 * M / 4 ∈ Icc 0 M := ⟨by positivity, by linarith⟩
  have h1 : M / 4 ∈ Icc 0 M := ⟨by positivity, by linarith⟩
  obtain ⟨b, hbdef⟩ : ∃ b, Ginv f (3 * M / 4) = b := ⟨_, rfl⟩
  have hbI : b ∈ Icc (0:ℝ) 1 := hbdef ▸ Ginv_mem hf h3
  have hGb : G f b = 3 * M / 4 := hbdef ▸ G_Ginv hf h3
  have hb0 : 0 < b := by
    rcases hbI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, G_zero] at hGb; linarith
  have hb1 : b < 1 := by
    rcases hbI.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hGb; linarith
  refine ⟨b, ⟨hb0, hb1⟩, ?_⟩
  rw [bid_eq hf ⟨hb0, hb1⟩ ⟨hb1.le, le_rfl⟩, hGb]
  have : M - 3 * M / 4 = M / 4 := by ring
  rw [this, ← hbdef]
  exact (Ginv_strictMonoOn hf).monotoneOn h1 h3 (by linarith)

lemma H_ge_of {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ bidFn f a 1) :
    c * (bidFnInv f a c)⁻¹ + (bidFn f a 1 - c) ≤ Hfun f a := by
  have hvh := vh_mem hf ha
  have hcI : c ∈ Icc 0 (bidFn f a 1) := ⟨hc0, hc⟩
  have h0I : (0:ℝ) ∈ Icc 0 (bidFn f a 1) := ⟨le_rfl, hvh.1.le⟩
  have hvI : bidFn f a 1 ∈ Icc 0 (bidFn f a 1) := ⟨hvh.1.le, le_rfl⟩
  unfold Hfun
  rw [← intervalIntegral.integral_add_adjacent_intervals (invinv_ii hf ha h0I hcI)
    (invinv_ii hf ha hcI hvI)]
  have h1 : ∫ s in (0:ℝ)..c, (bidFnInv f a c)⁻¹ ≤ ∫ s in (0:ℝ)..c, (bidFnInv f a s)⁻¹ := by
    apply intervalIntegral.integral_mono_on hc0 intervalIntegrable_const (invinv_ii hf ha h0I hcI)
    intro s hs
    have hsI : s ∈ Icc 0 (bidFn f a 1) := ⟨hs.1, hs.2.trans hc⟩
    exact inv_anti₀ (inv_pos hf ha hsI) ((inv_strictMonoOn hf ha).monotoneOn hsI hcI hs.2)
  have h2 : ∫ s in c..bidFn f a 1, (1:ℝ) ≤ ∫ s in c..bidFn f a 1, (bidFnInv f a s)⁻¹ := by
    apply intervalIntegral.integral_mono_on hc intervalIntegrable_const (invinv_ii hf ha hcI hvI)
    intro s hs
    have hsI : s ∈ Icc 0 (bidFn f a 1) := ⟨hc0.trans hs.1, hs.2⟩
    exact (one_le_inv₀ (inv_pos hf ha hsI)).2 (inv_mem hf ha hsI).2
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at h1 h2
  linarith

lemma exists_a {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) : ∃ a ∈ Ioo 0 b, 1 ≤ Hfun f a := by
  set M := G f 1
  have hM := G_one_pos hf
  set Gc := fun t => G f (max 0 (min t 1)) with hGc
  set Gi := fun s => Ginv f (max 0 (min s M)) with hGi
  have hGcc : Continuous Gc := Gc_cont hf
  have hGic : Continuous Gi := Gi_cont hf
  have hGc_eq : ∀ t ∈ Icc (0:ℝ) 1, Gc t = G f t := fun t ht => by simp only [hGc, clamp_eq ht]
  have hGi_eq : ∀ s ∈ Icc 0 M, Gi s = Ginv f s := fun s hs => by simp only [hGi, clamp_eq hs]
  set c : ℝ := 1 / 2
  have hcI : c ∈ Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set L := fun a => c * (Gi (Gc c + Gc a))⁻¹ + (Gi (Gc 1 - Gc a) - c) with hL
  set V := fun a => Gi (Gc 1 - Gc a) with hV
  have h00 : Gc 0 = 0 := by rw [hGc_eq 0 ⟨le_rfl, zero_le_one⟩, G_zero]
  have hden : Gi (Gc c + Gc 0) = c := by
    rw [h00, add_zero, hGc_eq c hcI, hGi_eq _ (G_mem hf hcI), Ginv_G hf hcI]
  have hV0 : V 0 = 1 := by
    simp only [hV]
    rw [h00, sub_zero, hGc_eq 1 ⟨zero_le_one, le_rfl⟩, hGi_eq _ ⟨hM.le, le_rfl⟩, Ginv_top hf]
  have hLc : ContinuousAt L 0 := by
    have hd : ContinuousAt (fun a => Gi (Gc c + Gc a)) 0 :=
      (hGic.comp (continuous_const.add hGcc)).continuousAt
    have hd' : ContinuousAt (fun a => (Gi (Gc c + Gc a))⁻¹) 0 :=
      hd.inv₀ (by rw [hden]; norm_num)
    exact (continuousAt_const.mul hd').add
      ((hGic.comp (continuous_const.sub hGcc)).continuousAt.sub continuousAt_const)
  have hL0 : L 0 = 3 / 2 := by
    simp only [hL]
    rw [hden]
    have : Gi (Gc 1 - Gc 0) = 1 := hV0
    rw [this]; norm_num
  have hVc : ContinuousAt V 0 := (hGic.comp (continuous_const.sub hGcc)).continuousAt
  have ev1 : ∀ᶠ a in 𝓝 0, 1 < L a := hLc.eventually (lt_mem_nhds (by rw [hL0]; norm_num))
  have ev2 : ∀ᶠ a in 𝓝 0, c < V a := hVc.eventually (lt_mem_nhds (by rw [hV0]; norm_num))
  have ev3 : ∀ᶠ a in 𝓝[>] (0:ℝ), a ∈ Ioo 0 b := Ioo_mem_nhdsGT hb.1
  obtain ⟨a, ⟨h1, h2⟩, h3⟩ :=
    ((ev1.and ev2).filter_mono nhdsWithin_le_nhds |>.and ev3).exists
  refine ⟨a, h3, ?_⟩
  have ha : a ∈ Ioo (0:ℝ) 1 := ⟨h3.1, h3.2.trans hb.2⟩
  have haI : a ∈ Icc (0:ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  have hVa : V a = bidFn f a 1 := by
    simp only [hV]
    rw [hGc_eq 1 ⟨zero_le_one, le_rfl⟩, hGc_eq a haI,
      hGi_eq _ (Gdiff_mem hf ha ⟨ha.2.le, le_rfl⟩), bid_eq hf ha ⟨ha.2.le, le_rfl⟩]
  rw [hVa] at h2
  have hcvh : c ∈ Icc 0 (bidFn f a 1) := ⟨hcI.1, h2.le⟩
  have hτ : Gi (Gc c + Gc a) = bidFnInv f a c := by
    rw [hGc_eq c hcI, hGc_eq a haI, hGi_eq _ (Gsum_mem' hf ha hcvh)]; rfl
  have hLa : L a = c * (bidFnInv f a c)⁻¹ + (bidFn f a 1 - c) := by
    simp only [hL]; rw [hτ]; rw [← hVa]
  have := H_ge_of hf ha hcI.1 h2.le
  linarith

lemma H_contOn {a b : ℝ} (ha : 0 < a) (hb : b < 1) : ContinuousOn (Hfun f) (Icc a b) := by
  set M := G f 1
  set Gc := fun t => G f (max 0 (min t 1)) with hGc
  set Gi := fun s => Ginv f (max 0 (min s M)) with hGi
  have hGcc : Continuous Gc := Gc_cont hf
  have hGic : Continuous Gi := Gi_cont hf
  have hGc_eq : ∀ t ∈ Icc (0:ℝ) 1, Gc t = G f t := fun t ht => by simp only [hGc, clamp_eq ht]
  have hGi_eq : ∀ s ∈ Icc 0 M, Gi s = Ginv f s := fun s hs => by simp only [hGi, clamp_eq hs]
  set K : ℝ → ℝ → ℝ := fun vl s => (max a (Gi (Gc s + Gc vl)))⁻¹ with hK
  have hKc : Continuous (Function.uncurry K) := by
    apply Continuous.inv₀
    · exact continuous_const.max (hGic.comp ((hGcc.comp continuous_snd).add (hGcc.comp continuous_fst)))
    · intro p; exact (ha.trans_le (le_max_left _ _)).ne'
  have hVc : Continuous (fun vl => Gi (Gc 1 - Gc vl)) := hGic.comp (continuous_const.sub hGcc)
  have hHc : Continuous (fun vl => ∫ s in (0:ℝ)..Gi (Gc 1 - Gc vl), K vl s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hKc hVc
  refine hHc.continuousOn.congr ?_
  intro vl hvl
  have hvl' : vl ∈ Ioo (0:ℝ) 1 := ⟨ha.trans_le hvl.1, hvl.2.trans_lt hb⟩
  have hvlI : vl ∈ Icc (0:ℝ) 1 := ⟨hvl'.1.le, hvl'.2.le⟩
  have hvh := vh_mem hf hvl'
  have hV : Gi (Gc 1 - Gc vl) = bidFn f vl 1 := by
    rw [hGc_eq 1 ⟨zero_le_one, le_rfl⟩, hGc_eq vl hvlI,
      hGi_eq _ (Gdiff_mem hf hvl' ⟨hvl'.2.le, le_rfl⟩), bid_eq hf hvl' ⟨hvl'.2.le, le_rfl⟩]
  unfold Hfun
  simp only
  rw [hV]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hvh.1.le] at hs
  simp only [hK]
  have hsI : s ∈ Icc (0:ℝ) 1 := ⟨hs.1, hs.2.trans hvh.2.le⟩
  have hτ : Gi (Gc s + Gc vl) = bidFnInv f vl s := by
    rw [hGc_eq s hsI, hGc_eq vl hvlI, hGi_eq _ (Gsum_mem' hf hvl' hs)]; rfl
  rw [hτ, max_eq_right (hvl.1.trans (inv_mem hf hvl' hs).1)]

theorem exists_bc : ∃ vl vh, BoundaryConds f vl vh := by
  obtain ⟨b, hb, hbb⟩ := exists_b hf
  obtain ⟨a, ha, haH⟩ := exists_a hf hb
  have hHb := H_le_of hf hb hbb
  have hivt := intermediate_value_Icc' (ha.2.le) (H_contOn hf ha.1 hb.2)
  obtain ⟨vl, hvlab, hH⟩ := hivt ⟨hHb, haH⟩
  have hvl : vl ∈ Ioo (0:ℝ) 1 := ⟨ha.1.trans_le hvlab.1, hvlab.2.trans_lt hb.2⟩
  have hvh := vh_mem hf hvl
  refine ⟨vl, bidFn f vl 1, ⟨⟨hvl.1.le, hvl.2.le⟩, rfl, ?_⟩⟩
  rw [alloc_integral hf hvl ⟨hvh.1.le, le_rfl⟩]
  exact hH

end Exist


section Eq15
variable {f : ℝ → ℝ} (hf : Assumption1 f)
include hf

lemma eq15_int {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1) :
    ∫ t in vl..1, f t / (Ginv f (G f t - G f vl) * f (Ginv f (G f t - G f vl))) = Hfun f vl := by
  have hvh := vh_mem hf hvl
  unfold Hfun
  rw [← alloc_integral hf hvl ⟨hvh.1.le, le_rfl⟩, inv_vh hf hvl,
    intervalIntegral.integral_of_le hvl.2.le, intervalIntegral.integral_of_le hvl.2.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : t ≠ 0 := (hvl.1.trans ht.1).ne'
  simp only
  rw [deriv_bid hf hvl ht, ← bid_eq hf hvl ⟨ht.1.le, ht.2.le⟩]
  unfold dbid
  field_simp

lemma H_le_ratio {vl : ℝ} (hvl : vl ∈ Ioo (0:ℝ) 1) : Hfun f vl ≤ bidFn f vl 1 / vl := by
  have hvh := vh_mem hf hvl
  unfold Hfun
  have h1 : ∫ s in (0:ℝ)..bidFn f vl 1, (bidFnInv f vl s)⁻¹ ≤ ∫ s in (0:ℝ)..bidFn f vl 1, vl⁻¹ := by
    apply intervalIntegral.integral_mono_on hvh.1.le
      (invinv_ii hf hvl ⟨le_rfl, hvh.1.le⟩ ⟨hvh.1.le, le_rfl⟩) intervalIntegrable_const
    intro s hs
    exact inv_anti₀ hvl.1 (inv_mem hf hvl hs).1
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← div_eq_mul_inv] at h1
  exact h1

lemma H_strictAntiOn : StrictAntiOn (Hfun f) (Ioo 0 1) := by
  intro v1 hv1 v2 hv2 h12
  have hvh1 := vh_mem hf hv1
  have hvh2 := vh_mem hf hv2
  set M := G f 1
  have hG12 := G_strictMonoOn hf ⟨hv1.1.le, hv1.2.le⟩ ⟨hv2.1.le, hv2.2.le⟩ h12
  have hvhlt : bidFn f v2 1 < bidFn f v1 1 := by
    rw [bid_eq hf hv1 ⟨hv1.2.le, le_rfl⟩, bid_eq hf hv2 ⟨hv2.2.le, le_rfl⟩]
    exact Ginv_strictMonoOn hf (Gdiff_mem hf hv2 ⟨hv2.2.le, le_rfl⟩)
      (Gdiff_mem hf hv1 ⟨hv1.2.le, le_rfl⟩) (by linarith)
  have h0I1 : (0:ℝ) ∈ Icc 0 (bidFn f v1 1) := ⟨le_rfl, hvh1.1.le⟩
  have hv2I1 : bidFn f v2 1 ∈ Icc 0 (bidFn f v1 1) := ⟨hvh2.1.le, hvhlt.le⟩
  have hv1I1 : bidFn f v1 1 ∈ Icc 0 (bidFn f v1 1) := ⟨hvh1.1.le, le_rfl⟩
  -- `τ₁ ≤ τ₂` on `[0, vh₂]`
  have hcmp : ∫ s in (0:ℝ)..bidFn f v2 1, (bidFnInv f v2 s)⁻¹ ≤
      ∫ s in (0:ℝ)..bidFn f v2 1, (bidFnInv f v1 s)⁻¹ := by
    apply intervalIntegral.integral_mono_on hvh2.1.le
      (invinv_ii hf hv2 ⟨le_rfl, hvh2.1.le⟩ ⟨hvh2.1.le, le_rfl⟩) (invinv_ii hf hv1 h0I1 hv2I1)
    intro s hs
    have hs1 : s ∈ Icc 0 (bidFn f v1 1) := ⟨hs.1, hs.2.trans hvhlt.le⟩
    apply inv_anti₀ (inv_pos hf hv1 hs1)
    unfold bidFnInv
    exact (Ginv_strictMonoOn hf).monotoneOn (Gsum_mem' hf hv1 hs1) (Gsum_mem' hf hv2 hs)
      (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (invinv_ii hf hv1 h0I1 hv2I1) (invinv_ii hf hv1 hv2I1 hv1I1)
  have htail : ∫ s in bidFn f v2 1..bidFn f v1 1, (1:ℝ) ≤
      ∫ s in bidFn f v2 1..bidFn f v1 1, (bidFnInv f v1 s)⁻¹ := by
    apply intervalIntegral.integral_mono_on hvhlt.le intervalIntegrable_const
      (invinv_ii hf hv1 hv2I1 hv1I1)
    intro s hs
    have hsI : s ∈ Icc 0 (bidFn f v1 1) := ⟨hvh2.1.le.trans hs.1, hs.2⟩
    exact (one_le_inv₀ (inv_pos hf hv1 hsI)).2 (inv_mem hf hv1 hsI).2
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at htail
  unfold Hfun
  linarith

lemma exists_H_one : ∃ vl ∈ Ioo (0:ℝ) 1, Hfun f vl = 1 := by
  obtain ⟨b, hb, hbb⟩ := exists_b hf
  obtain ⟨a, ha, haH⟩ := exists_a hf hb
  have hHb := H_le_of hf hb hbb
  obtain ⟨vl, hvlab, hH⟩ := intermediate_value_Icc' (ha.2.le) (H_contOn hf ha.1 hb.2) ⟨hHb, haH⟩
  exact ⟨vl, ⟨ha.1.trans_le hvlab.1, hvlab.2.trans_lt hb.2⟩, hH⟩

end Eq15

end DIThm2

theorem solution (f : ℝ → ℝ) (hf : DeferredInspection.SingleAgent.Assumption1 f) :
    (∃! vl, vl ∈ Ioo (0 : ℝ) 1 ∧
      ∫ t in vl..1,
        f t / (DeferredInspection.SingleAgent.Ginv f
            (DeferredInspection.SingleAgent.G f t - DeferredInspection.SingleAgent.G f vl) *
          f (DeferredInspection.SingleAgent.Ginv f
            (DeferredInspection.SingleAgent.G f t - DeferredInspection.SingleAgent.G f vl))) = 1) ∧
    ∀ vl ∈ Ioo (0 : ℝ) 1,
      (∫ t in vl..1,
        f t / (DeferredInspection.SingleAgent.Ginv f
            (DeferredInspection.SingleAgent.G f t - DeferredInspection.SingleAgent.G f vl) *
          f (DeferredInspection.SingleAgent.Ginv f
            (DeferredInspection.SingleAgent.G f t - DeferredInspection.SingleAgent.G f vl)))) = 1 →
      vl ≤ DeferredInspection.SingleAgent.bidFn f vl 1 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨vl, hvl, hH⟩ := DIThm2.exists_H_one hf
    refine ⟨vl, ⟨hvl, by rw [DIThm2.eq15_int hf hvl]; exact hH⟩, ?_⟩
    rintro w ⟨hw, hwH⟩
    rw [DIThm2.eq15_int hf hw] at hwH
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := DIThm2.H_strictAntiOn hf hw hvl h; linarith
    · have := DIThm2.H_strictAntiOn hf hvl hw h; linarith
  · intro vl hvl hH
    rw [DIThm2.eq15_int hf hvl] at hH
    have := DIThm2.H_le_ratio hf hvl
    rw [hH, le_div_iff₀ hvl.1, one_mul] at this
    exact this
