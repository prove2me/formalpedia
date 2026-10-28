-- Prove2me | solution 1 for DisruptReroute.GenEq.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T15:56:28.150324+00:00
-- url     : https://prove2.me/submissions/a3259a70-1ef2-422a-b1b3-c5d94ff7da6f

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

set_option autoImplicit false

namespace P87
open DisruptReroute.GenEq Set

variable {N : ℕ}

noncomputable def AObj (g : ℝ → ℝ) (cap π x : Fin N → ℝ) : ℝ :=
  (∫ t in (0:ℝ)..(∑ i ∈ active N cap, x i), g t) - ∑ i ∈ active N cap, π i * x i

def AEff (g : ℝ → ℝ) (cap π x : Fin N → ℝ) : Prop :=
  inBox cap x ∧ proportional cap π x ∧
    ∀ y, inBox cap y → AObj g cap π y ≤ AObj g cap π x

def AEq (g : ℝ → ℝ) (A : Set ℝ) (κ cap π : Fin N → ℝ) : Prop :=
  (∀ i ∈ active N cap, π i ∈ A) ∧ (∃ x, AEff g cap π x) ∧
  ∀ i ∈ active N cap, ∀ π' ∈ A, ∀ x, AEff g cap π x →
    ∀ x', AEff g cap (Function.update π i π') x' → (π i - κ i) * x i ≥ (π' - κ i) * x' i

structure MH (g : ℝ → ℝ) (Dm : ℝ) (cap : Fin N → ℝ) : Prop where
  cap_nn : ∀ i, 0 ≤ cap i
  tot_le : marketTotal cap ≤ Dm
  gc : ContinuousOn g (Icc 0 Dm)
  ga : StrictAntiOn g (Icc 0 Dm)

lemma upd_s (π : Fin N → ℝ) (i : Fin N) (v : ℝ) : Function.update π i v i = v := by simp

lemma upd_n (π : Fin N → ℝ) {i j : Fin N} (v : ℝ) (h : j ≠ i) :
    Function.update π i v j = π j := by simp [h]

lemma mem_active {cap : Fin N → ℝ} {i : Fin N} : i ∈ active N cap ↔ 0 < cap i := by
  simp [active]

lemma box_mem {cap x : Fin N → ℝ} (h : inBox cap x) {i : Fin N} (hi : i ∈ active N cap) :
    0 ≤ x i ∧ x i ≤ cap i := by
  have := h i; rwa [if_pos hi] at this

lemma box_nmem {cap x : Fin N → ℝ} (h : inBox cap x) {i : Fin N} (hi : i ∉ active N cap) :
    x i = 0 := by
  have := h i; rwa [if_neg hi] at this

lemma sum_nonneg_box {cap x : Fin N → ℝ} (h : inBox cap x) :
    0 ≤ ∑ i ∈ active N cap, x i :=
  Finset.sum_nonneg fun _ hi => (box_mem h hi).1

lemma sum_le_box {cap x : Fin N → ℝ} (h : inBox cap x) :
    ∑ i ∈ active N cap, x i ≤ marketTotal cap :=
  Finset.sum_le_sum fun _ hi => (box_mem h hi).2

lemma tot_nonneg {cap : Fin N → ℝ} (hc : ∀ i, 0 ≤ cap i) : 0 ≤ marketTotal cap :=
  Finset.sum_nonneg fun i _ => hc i

lemma MH.Dm0 {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) : 0 ≤ Dm :=
  le_trans (tot_nonneg H.cap_nn) H.tot_le

lemma MH.ii {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {a b : ℝ}
    (ha : 0 ≤ a) (haD : a ≤ Dm) (hb : 0 ≤ b) (hbD : b ≤ Dm) :
    IntervalIntegrable g MeasureTheory.volume a b :=
  (H.gc.mono (Set.uIcc_subset_Icc ⟨ha, haD⟩ ⟨hb, hbD⟩)).intervalIntegrable

lemma int_ge {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Dm) :
    (b - a) * g b ≤ ∫ t in a..b, g t := by
  have h1 : ∫ _ in a..b, g b = (b - a) * g b := by simp
  rw [← h1]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (H.ii ha (by linarith) (by linarith) hb)
  intro t ht
  exact H.ga.antitoneOn ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, hb⟩ ht.2

lemma int_le {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Dm) :
    ∫ t in a..b, g t ≤ (b - a) * g a := by
  have h1 : ∫ _ in a..b, g a = (b - a) * g a := by simp
  rw [← h1]
  apply intervalIntegral.integral_mono_on hab (H.ii ha (by linarith) (by linarith) hb)
    intervalIntegrable_const
  intro t ht
  exact H.ga.antitoneOn ⟨ha, by linarith⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩ ht.1

lemma obj_diff {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap)
    {x y : Fin N → ℝ} (hx : inBox cap x) (hy : inBox cap y) (π : Fin N → ℝ) :
    AObj g cap π y - AObj g cap π x =
      (∫ t in (∑ j ∈ active N cap, x j)..(∑ j ∈ active N cap, y j), g t) -
      (∑ j ∈ active N cap, π j * y j - ∑ j ∈ active N cap, π j * x j) := by
  unfold AObj
  have hxD := le_trans (sum_le_box hx) H.tot_le
  have hyD := le_trans (sum_le_box hy) H.tot_le
  rw [← intervalIntegral.integral_interval_sub_left
    (H.ii le_rfl H.Dm0 (sum_nonneg_box hy) hyD) (H.ii le_rfl H.Dm0 (sum_nonneg_box hx) hxD)]
  ring

def pert (x : Fin N → ℝ) (i : Fin N) (δ : ℝ) : Fin N → ℝ :=
  fun j => x j + if j = i then δ else 0

lemma pert_self (x : Fin N → ℝ) (i : Fin N) (δ : ℝ) : pert x i δ i = x i + δ := by
  simp [pert]

lemma pert_ne (x : Fin N → ℝ) {i j : Fin N} (δ : ℝ) (h : j ≠ i) : pert x i δ j = x j := by
  simp [pert, h]

lemma pert_sum {s : Finset (Fin N)} (x : Fin N → ℝ) {i : Fin N} (δ : ℝ) (hi : i ∈ s) :
    ∑ j ∈ s, pert x i δ j = ∑ j ∈ s, x j + δ := by
  simp [pert, Finset.sum_add_distrib, hi]

lemma pert_psum {s : Finset (Fin N)} (π x : Fin N → ℝ) {i : Fin N} (δ : ℝ) (hi : i ∈ s) :
    ∑ j ∈ s, π j * pert x i δ j = ∑ j ∈ s, π j * x j + π i * δ := by
  simp [pert, mul_add, Finset.sum_add_distrib, hi]

lemma pert_box {cap x : Fin N → ℝ} (h : inBox cap x) {i : Fin N} (hi : i ∈ active N cap)
    {δ : ℝ} (h0 : 0 ≤ x i + δ) (h1 : x i + δ ≤ cap i) : inBox cap (pert x i δ) := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [if_pos hi, pert_self]; exact ⟨h0, h1⟩
  · rw [pert_ne x δ hj]; exact h j

/-- Swap: mass never sits on a dearer seller while a cheaper one has room. -/
lemma E1 {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {π x : Fin N → ℝ}
    (hx : AEff g cap π x) {j k : Fin N}
    (hj : j ∈ active N cap) (hk : k ∈ active N cap) (hlt : π k < π j) (hpos : 0 < x j) :
    x k = cap k := by
  by_contra hne
  have hbk := box_mem hx.1 hk
  have hkl : x k < cap k := lt_of_le_of_ne hbk.2 hne
  have hjk : k ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ, 0 < δ ∧ δ ≤ x j ∧ δ ≤ cap k - x k :=
    ⟨min (x j) (cap k - x k), lt_min hpos (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hbj := box_mem hx.1 hj
  have hy1 : inBox cap (pert x j (-δ)) := pert_box hx.1 hj (by linarith) (by linarith)
  have hy1k : pert x j (-δ) k = x k := pert_ne x (-δ) hjk
  have hy : inBox cap (pert (pert x j (-δ)) k δ) :=
    pert_box hy1 hk (by rw [hy1k]; linarith) (by rw [hy1k]; linarith)
  have hs : ∑ l ∈ active N cap, pert (pert x j (-δ)) k δ l = ∑ l ∈ active N cap, x l := by
    rw [pert_sum _ _ hk, pert_sum _ _ hj]; ring
  have hp : ∑ l ∈ active N cap, π l * pert (pert x j (-δ)) k δ l =
      ∑ l ∈ active N cap, π l * x l - π j * δ + π k * δ := by
    rw [pert_psum _ _ _ hk, pert_psum _ _ _ hj]; ring
  have hle := hx.2.2 _ hy
  unfold AObj at hle
  rw [hs, hp] at hle
  nlinarith [mul_pos (sub_pos.2 hlt) hδ0]

/-- Marginal condition from above. -/
lemma E2 {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {π x : Fin N → ℝ}
    (hx : AEff g cap π x) {i : Fin N}
    (hi : i ∈ active N cap) (hlt : x i < cap i) : g (∑ j ∈ active N cap, x j) ≤ π i := by
  by_contra hcon
  push Not at hcon
  have hT0 := sum_nonneg_box hx.1
  have hTR : ∑ j ∈ active N cap, x j < marketTotal cap :=
    Finset.sum_lt_sum (fun j hj => (box_mem hx.1 hj).2) ⟨i, hi, hlt⟩
  have hRD := H.tot_le
  obtain ⟨δ0, hδ0, hc⟩ := Metric.continuousWithinAt_iff.1
    (H.gc _ ⟨hT0, by linarith⟩) (g (∑ j ∈ active N cap, x j) - π i) (by linarith)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ, 0 < δ ∧ δ < δ0 ∧ δ ≤ cap i - x i :=
    ⟨min (δ0/2) (cap i - x i), lt_min (by linarith) (by linarith),
     lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  have hbi := box_mem hx.1 hi
  have hy := pert_box hx.1 hi (δ := δ) (by linarith) (by linarith)
  have hs := pert_sum (s := active N cap) x δ hi
  have hp := pert_psum (s := active N cap) π x δ hi
  have hyD : ∑ j ∈ active N cap, x j + δ ≤ Dm := by
    have := sum_le_box hy; rw [hs] at this; linarith
  have hg : π i < g (∑ j ∈ active N cap, x j + δ) := by
    have h1 := hc (show ∑ j ∈ active N cap, x j + δ ∈ Icc 0 Dm from ⟨by linarith, hyD⟩)
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).1
    linarith
  have hint := int_ge H (a := ∑ j ∈ active N cap, x j) (b := ∑ j ∈ active N cap, x j + δ)
    hT0 (by linarith) hyD
  rw [show ∑ j ∈ active N cap, x j + δ - ∑ j ∈ active N cap, x j = δ by ring] at hint
  have hd := obj_diff H hx.1 hy π
  rw [hs, hp] at hd
  have hle := hx.2.2 _ hy
  nlinarith [mul_pos hδ (sub_pos.2 hg)]

/-- Marginal condition from below. -/
lemma E3 {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {π x : Fin N → ℝ}
    (hx : AEff g cap π x) {i : Fin N}
    (hi : i ∈ active N cap) (hpos : 0 < x i) : π i ≤ g (∑ j ∈ active N cap, x j) := by
  by_contra hcon
  push Not at hcon
  have hT0 := sum_nonneg_box hx.1
  have hTD : ∑ j ∈ active N cap, x j ≤ Dm := le_trans (sum_le_box hx.1) H.tot_le
  have hxT : x i ≤ ∑ j ∈ active N cap, x j :=
    Finset.single_le_sum (fun j hj => (box_mem hx.1 hj).1) hi
  obtain ⟨δ0, hδ0, hc⟩ := Metric.continuousWithinAt_iff.1
    (H.gc _ ⟨hT0, hTD⟩) (π i - g (∑ j ∈ active N cap, x j)) (by linarith)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ, 0 < δ ∧ δ < δ0 ∧ δ ≤ x i :=
    ⟨min (δ0/2) (x i), lt_min (by linarith) hpos,
     lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  have hbi := box_mem hx.1 hi
  have hy := pert_box hx.1 hi (δ := -δ) (by linarith) (by linarith)
  have hs := pert_sum (s := active N cap) x (-δ) hi
  have hp := pert_psum (s := active N cap) π x (-δ) hi
  have hg : g (∑ j ∈ active N cap, x j + -δ) < π i := by
    have h1 := hc (show ∑ j ∈ active N cap, x j + -δ ∈ Icc 0 Dm from
        ⟨by linarith, by linarith⟩)
      (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).2
    linarith
  have hint := int_le H (a := ∑ j ∈ active N cap, x j + -δ) (b := ∑ j ∈ active N cap, x j)
    (by linarith) (by linarith) hTD
  rw [show ∑ j ∈ active N cap, x j - (∑ j ∈ active N cap, x j + -δ) = δ by ring] at hint
  have hd := obj_diff H hx.1 hy π
  rw [hs, hp, intervalIntegral.integral_symm] at hd
  have hle := hx.2.2 _ hy
  nlinarith [mul_pos hδ (sub_pos.2 hg)]

/-- At the clearing price a seller is always fully served. -/
lemma L_full {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) {π x : Fin N → ℝ}
    (hx : AEff g cap π x) {i : Fin N} (hi : i ∈ active N cap)
    (hπ : π i = g (marketTotal cap)) : x i = cap i := by
  by_contra hne
  have hlt : x i < cap i := lt_of_le_of_ne (box_mem hx.1 hi).2 hne
  have h2 := E2 H hx hi hlt
  have hTR : ∑ j ∈ active N cap, x j < marketTotal cap :=
    Finset.sum_lt_sum (fun j hj => (box_mem hx.1 hj).2) ⟨i, hi, hlt⟩
  have hT0 := sum_nonneg_box hx.1
  have := H.ga ⟨hT0, by linarith [H.tot_le]⟩ ⟨by linarith, H.tot_le⟩ hTR
  linarith

lemma box_eq {cap : Fin N → ℝ} (hcap : ∀ i, 0 ≤ cap i) :
    {x : Fin N → ℝ | inBox cap x} = Set.pi Set.univ (fun i => Icc 0 (cap i)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  constructor
  · intro h i
    by_cases hi : i ∈ active N cap
    · exact box_mem h hi
    · have hc : cap i = 0 := le_antisymm (not_lt.1 (fun h' => hi (mem_active.2 h'))) (hcap i)
      rw [box_nmem h hi, hc]; exact ⟨le_rfl, le_rfl⟩
  · intro h i
    by_cases hi : i ∈ active N cap
    · rw [if_pos hi]; exact h i
    · rw [if_neg hi]
      have hc : cap i = 0 := le_antisymm (not_lt.1 (fun h' => hi (mem_active.2 h'))) (hcap i)
      have := h i; rw [hc] at this; exact le_antisymm this.2 this.1

lemma obj_cont {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) (π : Fin N → ℝ) :
    ContinuousOn (fun x => AObj g cap π x) {x | inBox cap x} := by
  have hD0 : 0 ≤ Dm := H.Dm0
  have hgcc : Continuous (fun t => g (max 0 (min t Dm))) :=
    H.gc.comp_continuous (by fun_prop)
      (fun t => ⟨le_max_left _ _, max_le hD0 (min_le_right _ _)⟩)
  have hF : Continuous (fun x : Fin N → ℝ =>
      (∫ t in (0:ℝ)..(∑ j ∈ active N cap, x j), g (max 0 (min t Dm))) -
        ∑ j ∈ active N cap, π j * x j) := by
    have hp := intervalIntegral.continuous_primitive
      (fun a b => hgcc.intervalIntegrable (μ := MeasureTheory.volume) a b) 0
    exact (hp.comp (continuous_finsetSum _ (fun j _ => continuous_apply j))).sub
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
  refine hF.continuousOn.congr ?_
  intro x hx
  have hx' : inBox cap x := hx
  simp only [AObj]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hT0 := sum_nonneg_box hx'
  have hTD := le_trans (sum_le_box hx') H.tot_le
  rw [Set.uIcc_of_le hT0] at ht
  simp only
  rw [min_eq_left (le_trans ht.2 hTD), max_eq_right ht.1]

noncomputable def propz (cap π x : Fin N → ℝ) : Fin N → ℝ := fun i =>
  if i ∈ active N cap then
    (∑ j ∈ (active N cap).filter (fun j => π j = π i), x j) /
      (∑ j ∈ (active N cap).filter (fun j => π j = π i), cap j) * cap i
  else 0

lemma grp_pos {cap π : Fin N → ℝ} {i : Fin N} (hi : i ∈ active N cap) :
    0 < ∑ j ∈ (active N cap).filter (fun j => π j = π i), cap j :=
  Finset.sum_pos (fun j hj => mem_active.1 (Finset.mem_filter.1 hj).1)
    ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩⟩

lemma propz_grp {cap π x : Fin N → ℝ} (v : ℝ) :
    ∑ j ∈ (active N cap).filter (fun j => π j = v), propz cap π x j =
    ∑ j ∈ (active N cap).filter (fun j => π j = v), x j := by
  rcases Finset.eq_empty_or_nonempty ((active N cap).filter (fun j => π j = v)) with he | ⟨i0, hi0⟩
  · simp [he]
  · have hm := Finset.mem_filter.1 hi0
    have hS := grp_pos (π := π) hm.1
    rw [hm.2] at hS
    have : ∀ j ∈ (active N cap).filter (fun j => π j = v), propz cap π x j =
        (∑ k ∈ (active N cap).filter (fun k => π k = v), x k) /
          (∑ k ∈ (active N cap).filter (fun k => π k = v), cap k) * cap j := by
      intro j hj
      have hj' := Finset.mem_filter.1 hj
      simp only [propz, if_pos hj'.1, hj'.2]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, div_mul_cancel₀ _ hS.ne']

lemma sums_eq_of_grp {cap π x y : Fin N → ℝ}
    (h : ∀ v, ∑ j ∈ (active N cap).filter (fun j => π j = v), y j =
      ∑ j ∈ (active N cap).filter (fun j => π j = v), x j) :
    ∑ j ∈ active N cap, y j = ∑ j ∈ active N cap, x j ∧
    ∑ j ∈ active N cap, π j * y j = ∑ j ∈ active N cap, π j * x j := by
  have e := fun (f : Fin N → ℝ) => (Finset.sum_fiberwise_of_maps_to (s := active N cap)
    (t := (active N cap).image π) (g := π) (f := f)
    (fun j hj => Finset.mem_image_of_mem π hj)).symm
  constructor
  · rw [e y, e x]
    exact Finset.sum_congr rfl (fun v _ => h v)
  · rw [e (fun j => π j * y j), e (fun j => π j * x j)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have h1 : ∀ z : Fin N → ℝ, ∑ j ∈ (active N cap).filter (fun j => π j = v), π j * z j =
        v * ∑ j ∈ (active N cap).filter (fun j => π j = v), z j := by
      intro z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2])
    rw [h1 y, h1 x, h v]

lemma propz_box {cap π x : Fin N → ℝ} (hx : inBox cap x) :
    inBox cap (propz cap π x) := by
  intro i
  by_cases hi : i ∈ active N cap
  · rw [if_pos hi]
    simp only [propz, if_pos hi]
    have hS := grp_pos (π := π) hi
    have hX0 : 0 ≤ ∑ j ∈ (active N cap).filter (fun j => π j = π i), x j :=
      Finset.sum_nonneg (fun j hj => (box_mem hx (Finset.mem_filter.1 hj).1).1)
    have hXS : ∑ j ∈ (active N cap).filter (fun j => π j = π i), x j ≤
        ∑ j ∈ (active N cap).filter (fun j => π j = π i), cap j :=
      Finset.sum_le_sum (fun j hj => (box_mem hx (Finset.mem_filter.1 hj).1).2)
    have hc := mem_active.1 hi
    have hr0 : 0 ≤ (∑ j ∈ (active N cap).filter (fun j => π j = π i), x j) /
        (∑ j ∈ (active N cap).filter (fun j => π j = π i), cap j) := div_nonneg hX0 hS.le
    have hr1 : (∑ j ∈ (active N cap).filter (fun j => π j = π i), x j) /
        (∑ j ∈ (active N cap).filter (fun j => π j = π i), cap j) ≤ 1 :=
      (div_le_one hS).2 hXS
    exact ⟨mul_nonneg hr0 hc.le, by nlinarith⟩
  · rw [if_neg hi]; simp [propz, hi]

lemma propz_prop {cap π x : Fin N → ℝ} : proportional cap π (propz cap π x) := by
  intro i hi j hj hij
  simp only [propz, if_pos hi, if_pos hj, hij]
  ring

lemma E0 {g : ℝ → ℝ} {Dm : ℝ} {cap : Fin N → ℝ} (H : MH g Dm cap) (π : Fin N → ℝ) :
    ∃ x, AEff g cap π x := by
  have hcomp : IsCompact {x : Fin N → ℝ | inBox cap x} := by
    rw [box_eq H.cap_nn]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  have hne : ({x : Fin N → ℝ | inBox cap x}).Nonempty :=
    ⟨0, fun i => by split_ifs <;> simp [H.cap_nn i]⟩
  obtain ⟨x, hx, hmax⟩ := hcomp.exists_isMaxOn hne (obj_cont H π)
  have hx' : inBox cap x := hx
  obtain ⟨h1, h2⟩ := sums_eq_of_grp (cap := cap) (π := π) (x := x) (y := propz cap π x)
    (fun v => propz_grp v)
  refine ⟨propz cap π x, propz_box hx', propz_prop, fun y hy => ?_⟩
  have : AObj g cap π (propz cap π x) = AObj g cap π x := by unfold AObj; rw [h1, h2]
  rw [this]
  exact isMaxOn_iff.1 hmax y hy

structure MK (g : ℝ → ℝ) (Dm : ℝ) (A : Set ℝ) (κ cap : Fin N → ℝ) : Prop
    extends MH g Dm cap where
  gcv : ConcaveOn ℝ (Set.Ioc 0 Dm) g
  hA : A.OrdConnected
  hgA : g (marketTotal cap) ∈ A
  hmr : (active N cap).Nonempty →
    DifferentiableAt ℝ (fun r => r * g r) (marketTotal cap) ∧
    ∀ i ∈ active N cap, κ i < deriv (fun r => r * g r) (marketTotal cap)

lemma dfacts {g : ℝ → ℝ} {Dm : ℝ} {A : Set ℝ} {κ cap : Fin N → ℝ} (H : MK g Dm A κ cap)
    (hne : (active N cap).Nonempty) :
    ∃ g' : ℝ, 0 < marketTotal cap ∧ g' ≤ 0 ∧
      (∀ i ∈ active N cap, κ i < g (marketTotal cap) + marketTotal cap * g') ∧
      ∀ Q, 0 < Q → Q < marketTotal cap →
        g Q ≤ g (marketTotal cap) + g' * (Q - marketTotal cap) := by
  obtain ⟨hd, hκ⟩ := H.hmr hne
  have hR0 : 0 < marketTotal cap := by
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos (fun j hj => mem_active.1 hj) ⟨i, hi⟩
  have hRD : marketTotal cap ≤ Dm := H.tot_le
  have hdiv := hd.hasDerivAt.div (hasDerivAt_id (marketTotal cap)) hR0.ne'
  have hg : HasDerivAt g ((deriv (fun r => r * g r) (marketTotal cap) * marketTotal cap -
      marketTotal cap * g (marketTotal cap)) / marketTotal cap ^ 2) (marketTotal cap) := by
    refine (hdiv.congr_deriv (by simp only [id, mul_one])).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hR0.ne'] with r hr
    show g r = r * g r / r
    exact (mul_div_cancel_left₀ (g r) hr).symm
  have hmem : marketTotal cap ∈ Set.Ioc 0 Dm := ⟨hR0, hRD⟩
  refine ⟨(deriv (fun r => r * g r) (marketTotal cap) * marketTotal cap -
      marketTotal cap * g (marketTotal cap)) / marketTotal cap ^ 2, hR0, ?_, fun i hi => ?_,
      fun Q hQ hQR => ?_⟩
  · have h1 := H.gcv.le_slope_of_hasDerivAt (x := marketTotal cap / 2)
      ⟨by linarith, by linarith⟩ hmem (by linarith) hg
    rw [slope_def_field] at h1
    have hanti : g (marketTotal cap) ≤ g (marketTotal cap / 2) :=
      H.ga.antitoneOn ⟨by linarith, by linarith⟩ ⟨hR0.le, hRD⟩ (by linarith)
    have h2 : (g (marketTotal cap) - g (marketTotal cap / 2)) /
        (marketTotal cap - marketTotal cap / 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have := hκ i hi
    have e : deriv (fun r => r * g r) (marketTotal cap) = g (marketTotal cap) +
        marketTotal cap * ((deriv (fun r => r * g r) (marketTotal cap) * marketTotal cap -
          marketTotal cap * g (marketTotal cap)) / marketTotal cap ^ 2) := by
      field_simp; ring
    linarith
  · have h1 := H.gcv.le_slope_of_hasDerivAt ⟨hQ, by linarith⟩ hmem hQR hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma key_lt {g : ℝ → ℝ} {R g' κ C q r : ℝ} (hR0 : 0 < R) (hg'0 : g' ≤ 0)
    (hκ : κ < g R + R * g') (htan : ∀ Q, 0 < Q → Q < R → g Q ≤ g R + g' * (Q - R))
    (hC : 0 ≤ C) (hCR : C + r = R) (hq0 : 0 ≤ q) (hqr : q < r) :
    (g (C + q) - κ) * q < (g R - κ) * r := by
  have hRg : R * g' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR0.le hg'0
  have hgk : κ < g R := by linarith
  rcases hq0.eq_or_lt with h0 | hq
  · rw [← h0]; simp only [mul_zero]; exact mul_pos (by linarith) (by linarith)
  · have hQ := htan (C + q) (by linarith) (by linarith)
    have hCq : C + q - R = q - r := by linarith
    rw [hCq] at hQ
    have h1 : (g (C + q) - κ) * q ≤ (g R + g' * (q - r) - κ) * q :=
      mul_le_mul_of_nonneg_right (by linarith) hq.le
    have hgq : g' * R ≤ g' * q := by nlinarith
    have h2 : 0 < (r - q) * (g R - κ + g' * q) := mul_pos (by linarith) (by nlinarith)
    nlinarith

lemma key_le {g : ℝ → ℝ} {R g' κ C q r : ℝ} (hR0 : 0 < R) (hg'0 : g' ≤ 0)
    (hκ : κ < g R + R * g') (htan : ∀ Q, 0 < Q → Q < R → g Q ≤ g R + g' * (Q - R))
    (hC : 0 ≤ C) (hCR : C + r = R) (hq0 : 0 ≤ q) (hqr : q ≤ r) :
    (g (C + q) - κ) * q ≤ (g R - κ) * r := by
  rcases hqr.lt_or_eq with h | h
  · exact (key_lt hR0 hg'0 hκ htan hC hCR hq0 h).le
  · rw [h, hCR]

lemma sum_others {cap y : Fin N → ℝ} {i : Fin N} (hi : i ∈ active N cap)
    (h : ∀ k ∈ active N cap, k ≠ i → y k = cap k) :
    ∑ j ∈ active N cap, y j = (marketTotal cap - cap i) + y i ∧
      0 ≤ marketTotal cap - cap i ∨ False := by
  left
  have e1 := Finset.add_sum_erase (active N cap) y hi
  have e2 := Finset.add_sum_erase (active N cap) cap hi
  have e3 : ∑ j ∈ (active N cap).erase i, y j = ∑ j ∈ (active N cap).erase i, cap j :=
    Finset.sum_congr rfl (fun k hk => h k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
  have e4 : 0 ≤ ∑ j ∈ (active N cap).erase i, cap j :=
    Finset.sum_nonneg (fun k hk => (mem_active.1 (Finset.mem_of_mem_erase hk)).le)
  have hR : marketTotal cap = ∑ j ∈ active N cap, cap j := rfl
  constructor <;> linarith

theorem fwd {g : ℝ → ℝ} {Dm : ℝ} {A : Set ℝ} {κ cap : Fin N → ℝ} (H : MK g Dm A κ cap)
    (π : Fin N → ℝ) (hπ : ∀ i ∈ active N cap, π i = g (marketTotal cap)) :
    AEq g A κ cap π := by
  refine ⟨fun i hi => (hπ i hi) ▸ H.hgA, E0 H.toMH π, ?_⟩
  intro i hi π' hπ' x hx x' hx'
  have hne : (active N cap).Nonempty := ⟨i, hi⟩
  obtain ⟨g', hR0, hg'0, hκ, htan⟩ := dfacts H hne
  have hxi : x i = cap i := L_full H.toMH hx hi (hπ i hi)
  have hb' := box_mem hx'.1 hi
  rw [hxi, hπ i hi]
  have hRg : marketTotal cap * g' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR0.le hg'0
  have hκi : κ i < g (marketTotal cap) := by linarith [hκ i hi]
  by_cases hle : π' ≤ g (marketTotal cap)
  · nlinarith [mul_le_mul_of_nonneg_right hle hb'.1,
      mul_le_mul_of_nonneg_left hb'.2 (sub_nonneg.2 hκi.le)]
  · push Not at hle
    rcases hb'.1.eq_or_lt with h0 | hpos
    · rw [← h0]; nlinarith [mul_pos (sub_pos.2 hκi) (mem_active.1 hi)]
    · have hfull : ∀ k ∈ active N cap, k ≠ i → x' k = cap k := by
        intro k hk hki
        refine E1 H.toMH hx' hi hk ?_ hpos
        rw [upd_n _ _ hki, upd_s, hπ k hk]; exact hle
      obtain ⟨hT, hC⟩ := (sum_others hi hfull).resolve_right id
      have hm := E3 H.toMH hx' hi hpos
      rw [upd_s, hT] at hm
      have hk := key_le hR0 hg'0 (hκ i hi) htan hC (by ring) hb'.1 hb'.2
      nlinarith [mul_le_mul_of_nonneg_right hm hb'.1]

set_option maxHeartbeats 1000000 in
theorem bwd {g : ℝ → ℝ} {Dm : ℝ} {A : Set ℝ} {κ cap : Fin N → ℝ} (H : MK g Dm A κ cap)
    {π : Fin N → ℝ} (heq : AEq g A κ cap π) :
    ∀ i ∈ active N cap, π i = g (marketTotal cap) := by
  obtain ⟨hπA, ⟨x, hx⟩, hdev⟩ := heq
  intro i0 hi0
  have hne : (active N cap).Nonempty := ⟨i0, hi0⟩
  obtain ⟨g', hR0, hg'0, hκ, htan⟩ := dfacts H hne
  have HH := H.toMH
  have hRg : marketTotal cap * g' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR0.le hg'0
  have hκR : ∀ i ∈ active N cap, κ i < g (marketTotal cap) := fun i hi => by
    linarith [hκ i hi]
  have devR : ∀ i ∈ active N cap,
      (π i - κ i) * x i ≥ (g (marketTotal cap) - κ i) * cap i := by
    intro i hi
    obtain ⟨x', hx'⟩ := E0 HH (Function.update π i (g (marketTotal cap)))
    have hx'i : x' i = cap i := L_full HH hx' hi (upd_s _ _ _)
    have := hdev i hi _ H.hgA x hx x' hx'
    rwa [hx'i] at this
  have low : ∀ i ∈ active N cap, g (marketTotal cap) ≤ π i := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have h1 := devR i hi
    have hb := box_mem hx.1 hi
    have hc := mem_active.1 hi
    have hk := hκR i hi
    by_cases hπκ : κ i ≤ π i
    · have hA1 := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.2 hπκ)
      have hA2 := mul_lt_mul_of_pos_right (sub_lt_sub_right hlt (κ i)) hc
      linarith
    · push Not at hπκ
      nlinarith [mul_pos (sub_pos.2 hk) hc, mul_nonneg (sub_nonneg.2 hπκ.le) hb.1]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (active N cap) π hne
  have high : π m ≤ g (marketTotal cap) := by
    by_contra hgt
    push Not at hgt
    have hb := box_mem hx.1 hm
    have hcm := mem_active.1 hm
    have hκm := hκR m hm
    have hdm := devR m hm
    rcases hb.1.eq_or_lt with h0 | hpos
    · rw [← h0] at hdm; nlinarith [mul_pos (sub_pos.2 hκm) hcm]
    have hT0 := sum_nonneg_box hx.1
    have hTle := sum_le_box hx.1
    have hRD := H.tot_le
    have hE3 := E3 HH hx hm hpos
    have hTR : ∑ j ∈ active N cap, x j < marketTotal cap := by
      rcases hTle.lt_or_eq with h | h
      · exact h
      · rw [h] at hE3; linarith
    have hxm : x m < cap m := by
      rcases hb.2.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk, hkl⟩ : ∃ k ∈ active N cap, x k < cap k := by
          by_contra hall
          push Not at hall
          have : marketTotal cap ≤ ∑ j ∈ active N cap, x j := Finset.sum_le_sum hall
          linarith
        rcases (hmax k hk).lt_or_eq with hlt | heq
        · exact hkl.ne (E1 HH hx hm hk hlt hpos)
        · have hp := hx.2.1 m hm k hk heq.symm
          rw [h] at hp
          nlinarith [mul_pos (sub_pos.2 hkl) hcm]
    have hE2 := E2 HH hx hm hxm
    by_cases hU : ∃ k ∈ active N cap, k ≠ m ∧ π k = π m
    · obtain ⟨k, hk, hkm, hkπ⟩ := hU
      have hsplit : ∀ y : Fin N → ℝ, ∑ j ∈ active N cap, y j =
          ∑ j ∈ (active N cap).filter (fun j => π j < π m), y j +
          ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), y j :=
        fun y => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hGmem : ∀ j, j ∈ (active N cap).filter (fun j => ¬ π j < π m) ↔
          j ∈ active N cap ∧ π j = π m := by
        intro j
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hj, hn⟩; exact ⟨hj, le_antisymm (hmax j hj) (not_lt.1 hn)⟩
        · rintro ⟨hj, he⟩; exact ⟨hj, by rw [he]; exact lt_irrefl _⟩
      have hLfull : ∑ j ∈ (active N cap).filter (fun j => π j < π m), x j =
          ∑ j ∈ (active N cap).filter (fun j => π j < π m), cap j :=
        Finset.sum_congr rfl (fun j hj =>
          E1 HH hx hm (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2 hpos)
      have hXG : (∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), x j) * cap m =
          x m * ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), cap j := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j hj =>
          hx.2.1 j ((hGmem j).1 hj).1 m hm ((hGmem j).1 hj).2)
      have hSG : cap m + cap k ≤ ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), cap j := by
        have hsub : ({m, k} : Finset (Fin N)) ⊆ (active N cap).filter (fun j => ¬ π j < π m) := by
          intro j hj
          rw [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl
          · exact (hGmem _).2 ⟨hm, rfl⟩
          · exact (hGmem _).2 ⟨hk, hkπ⟩
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => H.cap_nn j)
        rwa [Finset.sum_pair hkm.symm] at this
      have hck := mem_active.1 hk
      have hTsplit := hsplit x
      rw [hLfull] at hTsplit
      have hXgt : x m < ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), x j := by
        by_contra hh
        have h1 := mul_le_mul_of_nonneg_right (not_lt.1 hh) hcm.le
        have h2 : x m * cap m < x m *
            ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), cap j :=
          mul_lt_mul_of_pos_left (by linarith) hpos
        linarith
      obtain ⟨m0, hm0a, hm0b, hm0c⟩ : ∃ m0, m0 ≤ cap m ∧
          m0 ≤ ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), x j ∧ x m < m0 :=
        ⟨min (cap m) _, min_le_left _ _, min_le_right _ _, lt_min hxm hXgt⟩
      have hπκ : 0 < π m - κ m := by linarith
      obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε, 0 < ε ∧ ε ≤ (π m - g (marketTotal cap)) / 2 ∧
          ε * (2 * m0) ≤ (π m - κ m) * (m0 - x m) := by
        refine ⟨min ((π m - g (marketTotal cap)) / 2) ((π m - κ m) * (m0 - x m) / (2 * m0)),
          lt_min (by linarith) (div_pos (mul_pos hπκ (by linarith)) (by linarith)),
          min_le_left _ _, ?_⟩
        exact (le_div_iff₀ (by linarith)).1 (min_le_right _ _)
      have hπ'A : π m - ε ∈ A := H.hA.out H.hgA (hπA m hm) ⟨by linarith, by linarith⟩
      obtain ⟨x', hx'⟩ := E0 HH (Function.update π m (π m - ε))
      have hd := hdev m hm (π m - ε) hπ'A x hx x' hx'
      have hb' := box_mem hx'.1 hm
      have hx'm : m0 ≤ x' m := by
        by_contra hlt
        push Not at hlt
        have hlt' : x' m < cap m := lt_of_lt_of_le hlt hm0a
        have h2 := E2 HH hx' hm hlt'
        rw [upd_s] at h2
        have hT'0 := sum_nonneg_box hx'.1
        have hT'D := le_trans (sum_le_box hx'.1) H.tot_le
        have hTT' : ∑ j ∈ active N cap, x j < ∑ j ∈ active N cap, x' j := by
          by_contra hle
          push Not at hle
          have := H.ga.antitoneOn ⟨hT'0, hT'D⟩ ⟨hT0, by linarith⟩ hle
          linarith
        have hG0 : ∑ j ∈ (active N cap).filter (fun j => ¬ π j < π m), x' j = x' m := by
          apply Finset.sum_eq_single_of_mem m ((hGmem m).2 ⟨hm, rfl⟩)
          intro j hj hjm
          have hjG := (hGmem j).1 hj
          by_contra hne'
          have hpos' : 0 < x' j := lt_of_le_of_ne (box_mem hx'.1 hjG.1).1 (Ne.symm hne')
          have := E1 HH hx' hjG.1 hm (by rw [upd_s, upd_n _ _ hjm, hjG.2]; linarith) hpos'
          linarith
        have hL' : ∑ j ∈ (active N cap).filter (fun j => π j < π m), x' j ≤
            ∑ j ∈ (active N cap).filter (fun j => π j < π m), cap j :=
          Finset.sum_le_sum (fun j hj => (box_mem hx'.1 (Finset.mem_filter.1 hj).1).2)
        have hT' := hsplit x'
        rw [hG0] at hT'
        linarith
      have hπ'κ : 0 < π m - ε - κ m := by linarith
      have h3 : (π m - ε - κ m) * m0 ≤ (π m - ε - κ m) * x' m :=
        mul_le_mul_of_nonneg_left hx'm hπ'κ.le
      nlinarith [mul_pos hπκ (sub_pos.2 hm0c)]
    · push Not at hU
      have hfull : ∀ k ∈ active N cap, k ≠ m → x k = cap k := fun k hk hkm =>
        E1 HH hx hm hk (lt_of_le_of_ne (hmax k hk) (hU k hk hkm)) hpos
      obtain ⟨hT, hC⟩ := (sum_others hm hfull).resolve_right id
      have hgT : π m = g (marketTotal cap - cap m + x m) := by
        rw [← hT]; linarith
      have hk := key_lt hR0 hg'0 (hκ m hm) htan hC (by ring) hb.1 hxm
      rw [← hgT] at hk
      linarith
  exact le_antisymm (le_trans (hmax i0 hi0) high) (low i0 hi0)


/-! ## Part B: the network -/

section Net
variable {M : ℕ}

lemma dInv_sa {net : Network N M} (h : Standing net) (m : Fin M) :
    StrictAntiOn (net.dInv m) (Icc 0 (net.d m 0)) := by
  obtain ⟨-, -, -, hsa, hzero, -, hinv, hinv0, -⟩ := h.2.2.2.2.2.2.1 m
  intro y1 hy1 y2 hy2 hlt
  have h2 := hinv y2 hy2
  have hI2 : net.dInv m y2 ∈ {x | 0 < net.d m x} := by
    show 0 < net.d m _; rw [h2.2]; linarith [hy1.1]
  rcases hy1.1.eq_or_lt with h0 | hpos
  · rw [← h0, hinv0]
    rcases h2.1.2.lt_or_eq with hl | he
    · exact hl
    · exfalso; have := hzero _ he.ge; rw [h2.2] at this; linarith [hy1.1]
  · have h1 := hinv y1 hy1
    have hI1 : net.dInv m y1 ∈ {x | 0 < net.d m x} := by
      show 0 < net.d m _; rw [h1.2]; exact hpos
    by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hl | he
    · have := hsa hI1 hI2 hl; rw [h1.2, h2.2] at this; linarith
    · have := congrArg (net.d m) he; rw [h1.2, h2.2] at this; linarith

lemma dInv_cv {net : Network N M} (h : Standing net) (m : Fin M) :
    ConcaveOn ℝ (Ioc 0 (net.d m 0)) (net.dInv m) := by
  obtain ⟨-, -, hcv, hsa, -, -, hinv, -, -⟩ := h.2.2.2.2.2.2.1 m
  refine ⟨convex_Ioc _ _, ?_⟩
  intro a ha b hb t1 t2 ht1 ht2 ht
  have ea := (hinv a (Ioc_subset_Icc_self ha)).2
  have eb := (hinv b (Ioc_subset_Icc_self hb)).2
  have hIa : net.dInv m a ∈ {x | 0 < net.d m x} := by show 0 < net.d m _; rw [ea]; exact ha.1
  have hIb : net.dInv m b ∈ {x | 0 < net.d m x} := by show 0 < net.d m _; rw [eb]; exact hb.1
  have hy : t1 • a + t2 • b ∈ Ioc 0 (net.d m 0) := (convex_Ioc _ _) ha hb ht1 ht2 ht
  have ey := (hinv _ (Ioc_subset_Icc_self hy)).2
  have hIy : net.dInv m (t1 • a + t2 • b) ∈ {x | 0 < net.d m x} := by
    show 0 < net.d m _; rw [ey]; exact hy.1
  have hz := hcv.1 hIa hIb ht1 ht2 ht
  have hdz := hcv.2 hIa hIb ht1 ht2 ht
  rw [ea, eb] at hdz
  by_contra hlt
  have := hsa hIy hz (not_le.1 hlt)
  rw [ey] at this
  linarith

lemma sInv_sm {net : Network N M} (h : Standing net) (m : Fin M) :
    StrictMonoOn (net.sInv m) (Icc 0 (totalOrders net m)) := by
  obtain ⟨-, -, hsm, -, -, hinv, -⟩ := h.2.2.2.2.2.2.2 m
  intro y1 hy1 y2 hy2 hlt
  have e1 := (hinv y1 hy1).2
  have e2 := (hinv y2 hy2).2
  by_contra hle
  have := hsm.monotone (not_lt.1 hle)
  rw [e1, e2] at this; linarith

lemma sInv_cvx {net : Network N M} (h : Standing net) (m : Fin M) :
    ConvexOn ℝ (Icc 0 (totalOrders net m)) (net.sInv m) := by
  obtain ⟨-, hcv, hsm, -, -, hinv, -⟩ := h.2.2.2.2.2.2.2 m
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb t1 t2 ht1 ht2 ht
  have hy := (convex_Icc (0:ℝ) (totalOrders net m)) ha hb ht1 ht2 ht
  have hcs := hcv.2 (mem_univ (net.sInv m a)) (mem_univ (net.sInv m b)) ht1 ht2 ht
  rw [(hinv a ha).2, (hinv b hb).2] at hcs
  by_contra hlt
  have := hsm (not_le.1 hlt)
  rw [(hinv _ hy).2] at this
  linarith

lemma mt_eq {cap : Fin N → ℝ} (hc : ∀ i, 0 ≤ cap i) : marketTotal cap = ∑ i, cap i := by
  unfold marketTotal active
  exact Finset.sum_filter_of_ne (fun i _ hne => lt_of_le_of_ne (hc i) (Ne.symm hne))

lemma mt_mono {a b : Fin N → ℝ} (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    marketTotal a ≤ marketTotal b := by
  rw [mt_eq ha, mt_eq (fun i => le_trans (ha i) (hab i))]
  exact Finset.sum_le_sum (fun i _ => hab i)

lemma rbar_nn {net : Network N M} {Γ : Matrix N M} (hb : InBounds net Γ) (m : Fin M) (i : Fin N) :
    0 ≤ rbar Γ m i := Finset.sum_nonneg (fun j _ => (hb m i j).1)

lemma sbar_nn (net : Network N M) (Δ : Matrix N M) (m : Fin M) (i : Fin N) :
    0 ≤ sbar net Δ m i := le_max_left _ _

lemma mtR_le {net : Network N M} {Γ : Matrix N M} (hb : InBounds net Γ) (m : Fin M) :
    marketTotal (rbar Γ m) ≤ totalOrders net m := by
  rw [mt_eq (rbar_nn hb m)]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hb m i j).2))

lemma mtS_le {net : Network N M} (h : Standing net) {Δ : Matrix N M} (hb : InBounds net Δ)
    (m : Fin M) : marketTotal (sbar net Δ m) ≤ totalOrders net m := by
  rw [mt_eq (sbar_nn net Δ m)]
  unfold totalOrders
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have hθ := (h.2.2.2.2.1 m i).1
  have h0 : 0 ≤ ∑ j, Δ m j i := Finset.sum_nonneg (fun j _ => (hb m j i).1)
  have h1 : ∑ j, Δ m j i ≤ ∑ j, net.o m j i := Finset.sum_le_sum (fun j _ => (hb m j i).2)
  unfold sbar
  exact max_le (le_trans h0 h1) (by linarith)

lemma tot_le_d0 {net : Network N M} (h : Standing net) (m : Fin M) :
    totalOrders net m ≤ net.d m 0 := (h.2.2.2.2.2.2.1 m).2.2.2.2.2.1

lemma eStar_anti {net : Network N M} (h : Standing net) {Γ Γ' Δ Δ' : Matrix N M}
    (hΓ : InBounds net Γ) (hΓ' : InBounds net Γ') (hΔ : InBounds net Δ) (hΔ' : InBounds net Δ')
    (h1 : Γ ≤ Γ') (h2 : Δ ≤ Δ') (i : Fin N) :
    eStar net Γ' Δ' i ≤ eStar net Γ Δ i := by
  have T1 : ∑ m, (net.p m * ((∑ j, net.o m i j) - rbar Γ' m i)) +
      ∑ m, (priceStar net Γ' m * rbar Γ' m i - net.ι m i * rbar Γ' m i) ≤
      ∑ m, (net.p m * ((∑ j, net.o m i j) - rbar Γ m i)) +
      ∑ m, (priceStar net Γ m * rbar Γ m i - net.ι m i * rbar Γ m i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m _
    obtain ⟨-, -, -, -, -, -, hinv, -, -⟩ := h.2.2.2.2.2.2.1 m
    have hr0 := rbar_nn hΓ m i
    have hrr : rbar Γ m i ≤ rbar Γ' m i := Finset.sum_le_sum (fun j _ => h1 m i j)
    have hR0 := tot_nonneg (rbar_nn hΓ m)
    have hRR : marketTotal (rbar Γ m) ≤ marketTotal (rbar Γ' m) :=
      mt_mono (rbar_nn hΓ m) (fun k => Finset.sum_le_sum (fun j _ => h1 m k j))
    have hR'd := le_trans (mtR_le hΓ' m) (tot_le_d0 h m)
    have hPP : priceStar net Γ' m ≤ priceStar net Γ m :=
      (dInv_sa h m).antitoneOn ⟨hR0, by linarith⟩ ⟨by linarith, hR'd⟩ hRR
    have hPp : priceStar net Γ' m ≤ net.p m := (hinv _ ⟨by linarith, hR'd⟩).1.2
    have hι := (h.2.2.2.2.1 m i).2.2.1
    have c1 := mul_le_mul_of_nonpos_left hrr (by linarith : priceStar net Γ' m - net.p m - net.ι m i ≤ 0)
    have c2 := mul_le_mul_of_nonneg_right hPP hr0
    nlinarith
  have T2 : ∑ m, (net.b m i * sbar net Δ' m i - costStar net Δ' m * sbar net Δ' m i) -
      ∑ m, net.b m i * sbar net Δ' m i ≤
      ∑ m, (net.b m i * sbar net Δ m i - costStar net Δ m * sbar net Δ m i) -
      ∑ m, net.b m i * sbar net Δ m i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro m _
    obtain ⟨-, -, -, -, -, hinv, -⟩ := h.2.2.2.2.2.2.2 m
    have hs0 := sbar_nn net Δ m i
    have hss : sbar net Δ m i ≤ sbar net Δ' m i := by
      unfold sbar
      exact max_le_max le_rfl (by linarith [Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h2 m j i)])
    have hS0 := tot_nonneg (sbar_nn net Δ m)
    have hSS : marketTotal (sbar net Δ m) ≤ marketTotal (sbar net Δ' m) := by
      apply mt_mono (sbar_nn net Δ m)
      intro k; unfold sbar
      exact max_le_max le_rfl (by linarith [Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h2 m j k)])
    have hS'd := mtS_le h hΔ' m
    have hCC : costStar net Δ m ≤ costStar net Δ' m :=
      (sInv_sm h m).monotoneOn ⟨hS0, by linarith⟩ ⟨by linarith, hS'd⟩ hSS
    have hC0 : 0 ≤ costStar net Δ m := (hinv _ ⟨hS0, by linarith⟩).1
    have c1 := mul_le_mul_of_nonneg_left hss hC0
    have c2 := mul_le_mul_of_nonneg_right hCC (le_trans hs0 hss)
    nlinarith
  unfold eStar
  linarith

noncomputable def Fm (net : Network N M) (q : Matrix N M × Matrix N M) : Matrix N M × Matrix N M :=
  (PhiStar net q.1 q.2, PsiStar net q.1 q.2)

lemma cascade_succ (net : Network N M) (n : ℕ) :
    cascade net (n + 1) = Fm net (cascade net n) := by
  unfold cascade
  rw [Function.iterate_succ_apply']
  rfl

lemma Fm_bd {net : Network N M} (h : Standing net) (q : Matrix N M × Matrix N M) :
    InBounds net (Fm net q).1 ∧ InBounds net (Fm net q).2 := by
  constructor
  · intro m i j
    simp only [Fm, PhiStar]
    split_ifs
    · exact ⟨le_rfl, h.2.2.1 m i j⟩
    · exact ⟨h.2.2.1 m i j, le_rfl⟩
  · intro m i j
    simp only [Fm, PsiStar]
    split_ifs
    · exact ⟨le_rfl, h.2.2.1 m i j⟩
    · exact ⟨h.2.2.1 m i j, le_rfl⟩

lemma Fm_mono {net : Network N M} (h : Standing net) {q q' : Matrix N M × Matrix N M}
    (hq1 : InBounds net q.1) (hq2 : InBounds net q.2)
    (hq1' : InBounds net q'.1) (hq2' : InBounds net q'.2) (hle : q ≤ q') :
    Fm net q ≤ Fm net q' := by
  have he := eStar_anti h hq1 hq1' hq2 hq2' hle.1 hle.2
  refine ⟨fun m i j => ?_, fun m i j => ?_⟩
  · simp only [Fm, PhiStar]
    have := he j
    split_ifs with ha hb hb
    · exact le_rfl
    · exact h.2.2.1 m i j
    · exact absurd (le_trans hb this) ha
    · exact le_rfl
  · simp only [Fm, PsiStar]
    have := he i
    split_ifs with ha hb hb
    · exact le_rfl
    · exact h.2.2.1 m i j
    · exact absurd (le_trans hb this) ha
    · exact le_rfl

lemma cascade_bd {net : Network N M} (h : Standing net) (n : ℕ) :
    InBounds net (cascade net n).1 ∧ InBounds net (cascade net n).2 := by
  cases n with
  | zero =>
    constructor <;> intro m i j <;> exact ⟨le_rfl, h.2.2.1 m i j⟩
  | succ n => rw [cascade_succ]; exact Fm_bd h _

lemma cascade_mono {net : Network N M} (h : Standing net) : Monotone (cascade net) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    rw [cascade_succ]
    have hb := Fm_bd h (cascade net 0)
    exact ⟨fun m i j => (hb.1 m i j).1, fun m i j => (hb.2 m i j).1⟩
  | succ n ih =>
    rw [cascade_succ net (n + 1), cascade_succ net n]
    exact Fm_mono h (cascade_bd h n).1 (cascade_bd h n).2
      (Fm_bd h _).1 (Fm_bd h _).2 (by rw [← cascade_succ]; exact ih)

def ZO (net : Network N M) : Set (Matrix N M × Matrix N M) :=
  {q | ∀ m i j, (q.1 m i j = 0 ∨ q.1 m i j = net.o m i j) ∧
    (q.2 m i j = 0 ∨ q.2 m i j = net.o m i j)}

lemma ZO_finite (net : Network N M) : (ZO net).Finite := by
  apply (Set.finite_range (fun b : (Fin M → Fin N → Fin N → Bool) × (Fin M → Fin N → Fin N → Bool) =>
    ((fun m i j => if b.1 m i j then net.o m i j else 0 : Matrix N M),
     (fun m i j => if b.2 m i j then net.o m i j else 0 : Matrix N M)))).subset
  intro q hq
  refine ⟨(fun m i j => decide (q.1 m i j = net.o m i j),
    fun m i j => decide (q.2 m i j = net.o m i j)), ?_⟩
  ext m i j
  · simp only [decide_eq_true_eq]
    split_ifs with h1
    · exact h1.symm
    · rcases (hq m i j).1 with h0 | ho
      · exact h0.symm
      · exact absurd ho h1
  · simp only [decide_eq_true_eq]
    split_ifs with h1
    · exact h1.symm
    · rcases (hq m i j).2 with h0 | ho
      · exact h0.symm
      · exact absurd ho h1

lemma cascade_ZO (net : Network N M) (n : ℕ) : cascade net n ∈ ZO net := by
  cases n with
  | zero => intro m i j; exact ⟨Or.inl rfl, Or.inl rfl⟩
  | succ n =>
    rw [cascade_succ]
    intro m i j
    simp only [Fm, PhiStar, PsiStar]
    constructor
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

lemma stable_eu {net : Network N M} (h : Standing net) :
    ∃ Γ Δ : Matrix N M, IsMarketStableState net Γ Δ ∧
      ∀ Γ' Δ', IsMarketStableState net Γ' Δ' → Γ' = Γ ∧ Δ' = Δ := by
  haveI : Finite (ZO net) := (ZO_finite net).to_subtype
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨cascade net n, cascade_ZO net n⟩ : ZO net))
  have he' : cascade net a = cascade net b := congrArg Subtype.val he
  have hmono := cascade_mono h
  have key : ∀ a b : ℕ, a < b → cascade net a = cascade net b →
      ∃ q, Fm net q = q ∧ ∀ n ≥ a, cascade net n = q := by
    intro a b hab he
    have hfix : cascade net (a + 1) = cascade net a :=
      le_antisymm (he ▸ hmono (Nat.succ_le_of_lt hab)) (hmono (Nat.le_succ a))
    refine ⟨cascade net a, by rw [← cascade_succ]; exact hfix, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n _ ih => rw [cascade_succ, ih, ← cascade_succ, hfix]
  obtain ⟨q, hq, hev⟩ : ∃ q, Fm net q = q ∧ ∃ a, ∀ n ≥ a, cascade net n = q := by
    rcases lt_or_gt_of_ne hab with hl | hl
    · obtain ⟨q, h1, h2⟩ := key a b hl he'; exact ⟨q, h1, a, h2⟩
    · obtain ⟨q, h1, h2⟩ := key b a hl he'.symm; exact ⟨q, h1, b, h2⟩
  obtain ⟨a0, ha0⟩ := hev
  have ht : Filter.Tendsto (cascade net) Filter.atTop (nhds q) := tendsto_atTop_of_eventually_const ha0
  refine ⟨q.1, q.2, ⟨ht, ?_⟩, fun Γ' Δ' hs => ?_⟩
  · exact (congrArg id hq).symm
  · have := tendsto_nhds_unique hs.1 ht
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

lemma fix_adm {net : Network N M} {Γ Δ : Matrix N M} (hs : IsMarketStableState net Γ Δ) :
    Admissible net Γ ∧ Admissible net Δ := by
  have h1 : Γ = PhiStar net Γ Δ := congrArg Prod.fst hs.2
  have h2 : Δ = PsiStar net Γ Δ := congrArg Prod.snd hs.2
  constructor
  · intro m i j; rw [h1]; simp only [PhiStar]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro m i j; rw [h2]; simp only [PsiStar]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma adm_bd {net : Network N M} (h : Standing net) {Γ : Matrix N M} (ha : Admissible net Γ) :
    InBounds net Γ := by
  intro m i j
  rcases ha m i j with h0 | ho
  · rw [h0]; exact ⟨le_rfl, h.2.2.1 m i j⟩
  · rw [ho]; exact ⟨h.2.2.1 m i j, le_rfl⟩

lemma MKR {net : Network N M} {m' : Fin M} (h : Standing net) {Γ : Matrix N M} (hb : InBounds net Γ)
    (hmr : MarginalRevenue net m' (rbar Γ m')) :
    MK (net.dInv m') (net.d m' 0) (Ici 0) (net.ι m') (rbar Γ m') where
  cap_nn := rbar_nn hb m'
  tot_le := le_trans (mtR_le hb m') (tot_le_d0 h m')
  gc := (h.2.2.2.2.2.2.1 m').2.2.2.2.2.2.2.2
  ga := dInv_sa h m'
  gcv := dInv_cv h m'
  hA := ordConnected_Ici
  hgA := ((h.2.2.2.2.2.2.1 m').2.2.2.2.2.2.1 _
    ⟨tot_nonneg (rbar_nn hb m'), le_trans (mtR_le hb m') (tot_le_d0 h m')⟩).1.1
  hmr := hmr

lemma MKS {net : Network N M} {m' : Fin M} (h : Standing net) {Δ : Matrix N M} (hb : InBounds net Δ)
    (hmc : MarginalCost net m' (sbar net Δ m')) :
    MK (fun r => -(net.sInv m' r)) (totalOrders net m') (Iic 0) (fun i => -(net.b m' i))
      (sbar net Δ m') where
  cap_nn := sbar_nn net Δ m'
  tot_le := mtS_le h hb m'
  gc := (h.2.2.2.2.2.2.2 m').2.2.2.2.2.2.neg
  ga := fun a ha b hb' hab => neg_lt_neg ((sInv_sm h m') ha hb' hab)
  gcv := ((sInv_cvx h m').neg).subset Ioc_subset_Icc_self (convex_Ioc _ _)
  hA := ordConnected_Iic
  hgA := by
    show -(net.sInv m' _) ≤ 0
    exact neg_nonpos.2 ((h.2.2.2.2.2.2.2 m').2.2.2.2.2.1 _
      ⟨tot_nonneg (sbar_nn net Δ m'), mtS_le h hb m'⟩).1
  hmr := by
    intro hne
    obtain ⟨hd, hlt⟩ := hmc hne
    have e : (fun r => r * -(net.sInv m' r)) = fun r => -(r * net.sInv m' r) := by
      funext r; ring
    rw [e]
    refine ⟨hd.neg, fun i hi => ?_⟩
    have e2 : deriv (fun r => -(r * net.sInv m' r)) (marketTotal (sbar net Δ m')) =
        -deriv (fun x => x * net.sInv m' x) (marketTotal (sbar net Δ m')) := deriv.neg
    rw [e2]
    exact neg_lt_neg (hlt i hi)

lemma upd_neg (cost : Fin N → ℝ) (i : Fin N) (π' : ℝ) :
    Function.update (fun j => -cost j) i π' = fun j => -(Function.update cost i (-π') j) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

lemma effS_iff {net : Network N M} (m : Fin M) (cap cost x : Fin N → ℝ) :
    EfficientS net m cap cost x ↔ AEff (fun r => -(net.sInv m r)) cap (fun i => -cost i) x := by
  have hobj : ∀ y, switchObjective net m cap cost y =
      AObj (fun r => -(net.sInv m r)) cap (fun i => -cost i) y := by
    intro y
    simp only [switchObjective, AObj, intervalIntegral.integral_neg, neg_mul,
      Finset.sum_neg_distrib]
    ring
  have hprop : proportional cap cost x ↔ proportional cap (fun i => -cost i) x := by
    simp only [proportional, neg_inj]
  unfold EfficientS AEff
  rw [hprop]
  simp only [hobj]

lemma partialS_iff {net : Network N M} (m : Fin M) (cap cost : Fin N → ℝ) :
    PartialS net m cap cost ↔ AEq (fun r => -(net.sInv m r)) (Iic 0) (fun i => -(net.b m i)) cap
      (fun i => -cost i) := by
  constructor
  · rintro ⟨h1, ⟨x0, hx0⟩, h3⟩
    refine ⟨fun i hi => neg_nonpos.2 (h1 i hi), ⟨x0, (effS_iff m cap cost x0).1 hx0⟩, ?_⟩
    intro i hi π' hπ' x hx x' hx'
    rw [upd_neg] at hx'
    have := h3 i hi (-π') (neg_nonneg.2 hπ') x ((effS_iff m cap cost x).2 hx) x'
      ((effS_iff m cap _ x').2 hx')
    nlinarith
  · rintro ⟨h1, ⟨x0, hx0⟩, h3⟩
    refine ⟨fun i hi => neg_nonpos.1 (h1 i hi), ⟨x0, (effS_iff m cap cost x0).2 hx0⟩, ?_⟩
    intro i hi c' hc' x hx x' hx'
    have hx'' : AEff (fun r => -(net.sInv m r)) cap
        (Function.update (fun j => -cost j) i (-c')) x' := by
      rw [upd_neg, neg_neg]; exact (effS_iff m cap _ x').1 hx'
    have := h3 i hi (-c') (neg_nonpos.2 hc') x ((effS_iff m cap cost x).1 hx) x' hx''
    nlinarith

end Net

end P87

open DisruptReroute.GenEq in
theorem solution {N M : ℕ} (net : Network N M)
    (h : Standing net)
    (hMR : ∀ Γ : Matrix N M, Admissible net Γ →
      ∀ m : Fin M, MarginalRevenue net m (rbar Γ m))
    (hMC : ∀ Δ : Matrix N M, Admissible net Δ →
      ∀ m : Fin M, MarginalCost net m (sbar net Δ m)) :
    ∃! q : Profile N M × Profile N M × Matrix N M × Matrix N M,
      IsGeneralEquilibrium net q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨Γ, Δ, hst, huniq⟩ := P87.stable_eu h
  obtain ⟨haΓ, haΔ⟩ := P87.fix_adm hst
  have hbΓ := P87.adm_bd h haΓ
  have hbΔ := P87.adm_bd h haΔ
  refine ⟨(fun m _ => priceStar net Γ m, fun m _ => costStar net Δ m, Γ, Δ),
    ⟨fun m => ⟨?_, fun _ _ => rfl⟩, fun m => ⟨?_, fun _ _ => rfl⟩, hst⟩, ?_⟩
  · exact P87.fwd (P87.MKR h hbΓ (hMR Γ haΓ m)) _ (fun _ _ => rfl)
  · exact (P87.partialS_iff m _ _).2 (P87.fwd (P87.MKS h hbΔ (hMC Δ haΔ m)) _ (fun _ _ => rfl))
  · rintro ⟨π, c, Γ', Δ'⟩ ⟨hR, hS, hst'⟩
    obtain ⟨rfl, rfl⟩ := huniq Γ' Δ' hst'
    have hπ : π = fun m _ => priceStar net Γ' m := by
      funext m i
      by_cases hi : i ∈ active N (rbar Γ' m)
      · exact P87.bwd (P87.MKR h hbΓ (hMR Γ' haΓ m)) (hR m).1 i hi
      · exact (hR m).2 i hi
    have hc : c = fun m _ => costStar net Δ' m := by
      funext m i
      by_cases hi : i ∈ active N (sbar net Δ' m)
      · have := P87.bwd (P87.MKS h hbΔ (hMC Δ' haΔ m)) ((P87.partialS_iff m _ _).1 (hS m).1) i hi
        exact neg_inj.1 this
      · exact (hS m).2 i hi
    rw [hπ, hc]
