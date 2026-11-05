-- Prove2me | solution 1 for CoffmanMitrani.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T16:45:57.111986+00:00
-- url     : https://prove2.me/submissions/da48f006-3361-4ba9-93e6-531fa4026a35

import Mathlib
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_Achievable
import Definitions.Def_CoffmanMitrani_H
import Definitions.Def_CoffmanMitrani_present
import Definitions.Def_CoffmanMitrani_responseTime
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! D1 for e14b429d (CoffmanMitrani.priority_achievable): the finite Skorokhod identity.
For a finite job set `F` with arrival times `a` and nonnegative requirements `r`, the left-limit
workload `Wl t` (closed form) satisfies
  volume {s < t | 0 < Wl s} = (work arrived before t) - Wl t.
Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Set

namespace CMQ

variable {ι : Type*}

/-- work of jobs of `F` arriving in `[x, t)`. -/
noncomputable def Ain (F : Finset ι) (a r : ι → ℝ) (x t : ℝ) : ℝ :=
  ∑ l ∈ F.filter (fun l => x ≤ a l ∧ a l < t), r l

/-- work of jobs of `F` arriving exactly at `p`. -/
noncomputable def Jat (F : Finset ι) (a r : ι → ℝ) (p : ℝ) : ℝ :=
  ∑ l ∈ F.filter (fun l => a l = p), r l

/-- work of jobs of `F` arriving strictly before `t`. -/
noncomputable def Abef (F : Finset ι) (a r : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ l ∈ F.filter (fun l => a l < t), r l

/-- left-limit workload at `t` (closed form, arrivals strictly before `t`). -/
noncomputable def Wl (F : Finset ι) (a r : ι → ℝ) (t : ℝ) : ℝ :=
  ((F.filter (fun k => a k < t)).sup
    (fun k => (Ain F a r (a k) t - (t - a k)).toNNReal) : NNReal)

variable (F : Finset ι) (a r : ι → ℝ)

lemma Wl_nonneg (t : ℝ) : 0 ≤ Wl F a r t := NNReal.coe_nonneg _

lemma Wl_le_iff (t c : ℝ) :
    Wl F a r t ≤ c ↔ 0 ≤ c ∧ ∀ k ∈ F, a k < t → Ain F a r (a k) t - (t - a k) ≤ c := by
  constructor
  · intro h
    have h0 : 0 ≤ c := le_trans (Wl_nonneg F a r t) h
    refine ⟨h0, fun k hk hkt => ?_⟩
    have hs := Finset.le_sup (s := F.filter (fun k => a k < t)) (f := fun k => (Ain F a r (a k) t - (t - a k)).toNNReal)
      (Finset.mem_filter.2 ⟨hk, hkt⟩)
    have h1 : Ain F a r (a k) t - (t - a k) ≤ ((Ain F a r (a k) t - (t - a k)).toNNReal : ℝ) :=
      Real.le_coe_toNNReal _
    have h2 := NNReal.coe_le_coe.2 hs
    exact le_trans h1 (le_trans h2 h)
  · rintro ⟨h0, h⟩
    have hs : (F.filter (fun k => a k < t)).sup
        (fun k => (Ain F a r (a k) t - (t - a k)).toNNReal) ≤ c.toNNReal := by
      apply Finset.sup_le
      intro k hk
      rw [Finset.mem_filter] at hk
      exact Real.toNNReal_le_toNNReal (h k hk.1 hk.2)
    have := NNReal.coe_le_coe.2 hs
    rw [Real.coe_toNNReal _ h0] at this
    exact this

lemma term_le_Wl (t : ℝ) (k : ι) (hk : k ∈ F) (hkt : a k < t) :
    Ain F a r (a k) t - (t - a k) ≤ Wl F a r t :=
  ((Wl_le_iff F a r t _).1 le_rfl).2 k hk hkt

lemma Ain_self (p : ℝ) : Ain F a r p p = 0 := by
  unfold Ain
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_filter] at hl
  exact absurd (lt_of_le_of_lt hl.2.1 hl.2.2) (lt_irrefl _)

open Classical in
/-- splitting `[x, s)` at the last arrival `p` before `s`. -/
lemma Ain_split {x p s : ℝ} (hxp : x ≤ p) (hps : p < s)
    (hgap : ∀ l ∈ F, a l < s → a l ≤ p) :
    Ain F a r x s = Ain F a r x p + Jat F a r p := by
  unfold Ain Jat
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext l
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hl, h1, h2⟩
      rcases lt_or_eq_of_le (hgap l hl h2) with h3 | h3
      · exact Or.inl ⟨hl, h1, h3⟩
      · exact Or.inr ⟨hl, h3⟩
    · rintro (⟨hl, h1, h2⟩ | ⟨hl, h3⟩)
      · exact ⟨hl, h1, lt_trans h2 hps⟩
      · exact ⟨hl, h3 ▸ hxp, h3 ▸ hps⟩
  · rw [Finset.disjoint_filter]
    intro l _ h1 h2
    rw [h2] at h1
    exact lt_irrefl _ h1.2

open Classical in
lemma Abef_split {p t : ℝ} (hpt : p < t) (hgap : ∀ l ∈ F, a l < t → a l ≤ p) :
    Abef F a r t = Abef F a r p + Jat F a r p := by
  unfold Abef Jat
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext l
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hl, h2⟩
      rcases lt_or_eq_of_le (hgap l hl h2) with h3 | h3
      · exact Or.inl ⟨hl, h3⟩
      · exact Or.inr ⟨hl, h3⟩
    · rintro (⟨hl, h2⟩ | ⟨hl, h3⟩)
      · exact ⟨hl, lt_trans h2 hpt⟩
      · exact ⟨hl, h3 ▸ hpt⟩
  · rw [Finset.disjoint_filter]
    intro l _ h1 h2
    rw [h2] at h1
    exact lt_irrefl _ h1

lemma term_le_Wl' (p : ℝ) (k : ι) (hk : k ∈ F) (hkp : a k ≤ p) :
    Ain F a r (a k) p - (p - a k) ≤ Wl F a r p := by
  rcases lt_or_eq_of_le hkp with h | h
  · exact term_le_Wl F a r p k hk h
  · rw [h, Ain_self, sub_self, sub_zero]
    exact Wl_nonneg F a r p

/-- the workload between arrivals: drains at unit rate from `Wl p + Jat p`. -/
lemma Wl_step {p s : ℝ} (hps : p < s) (k0 : ι) (hk0 : k0 ∈ F) (hk0p : a k0 = p)
    (hgap : ∀ l ∈ F, a l < s → a l ≤ p) :
    Wl F a r s = max 0 (Wl F a r p + Jat F a r p - (s - p)) := by
  apply le_antisymm
  · rw [Wl_le_iff]
    refine ⟨le_max_left _ _, fun k hk hks => ?_⟩
    have hkp := hgap k hk hks
    rw [Ain_split F a r hkp hps hgap]
    have := term_le_Wl' F a r p k hk hkp
    exact le_trans (by linarith) (le_max_right _ _)
  · apply max_le (Wl_nonneg F a r s)
    have hJ : Jat F a r p - (s - p) ≤ Wl F a r s := by
      have := term_le_Wl F a r s k0 hk0 (hk0p ▸ hps)
      rw [Ain_split F a r (le_of_eq hk0p) hps hgap, hk0p, Ain_self, zero_add] at this
      exact this
    have hW : Wl F a r p ≤ Wl F a r s - Jat F a r p + (s - p) := by
      rw [Wl_le_iff]
      refine ⟨by linarith, fun k hk hkp => ?_⟩
      have := term_le_Wl F a r s k hk (lt_trans hkp hps)
      rw [Ain_split F a r (le_of_lt hkp) hps hgap] at this
      linarith
    linarith

lemma Wl_le_Abef (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) : Wl F a r t ≤ Abef F a r t := by
  rw [Wl_le_iff]
  refine ⟨Finset.sum_nonneg (fun l hl => hr l (Finset.mem_filter.1 hl).1), fun k hk hkt => ?_⟩
  have h1 : Ain F a r (a k) t ≤ Abef F a r t := by
    unfold Ain Abef
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      simp only [Finset.mem_filter] at hl ⊢
      exact ⟨hl.1, hl.2.2⟩
    · intro l hl _
      exact hr l (Finset.mem_filter.1 hl).1
  linarith

lemma Jat_nonneg (hr : ∀ l ∈ F, 0 ≤ r l) (p : ℝ) : 0 ≤ Jat F a r p :=
  Finset.sum_nonneg (fun l hl => hr l (Finset.mem_filter.1 hl).1)

/-- **D1, finite Skorokhod identity.** -/
theorem busy_eq (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) :
    volume {s : ℝ | s < t ∧ 0 < Wl F a r s} =
      ENNReal.ofReal (Abef F a r t - Wl F a r t) := by
  induction hn : (F.filter (fun l => a l < t)).card using Nat.strong_induction_on
    generalizing t with
  | _ n ih =>
  by_cases hne : (F.filter (fun l => a l < t)).Nonempty
  · set p := ((F.filter (fun l => a l < t)).image a).max' (hne.image a) with hp
    obtain ⟨k0, hk0f, hk0p⟩ := Finset.mem_image.1 (Finset.max'_mem _ (hne.image a))
    rw [← hp] at hk0p
    have hk0F : k0 ∈ F := (Finset.mem_filter.1 hk0f).1
    have hpt : p < t := hk0p ▸ (Finset.mem_filter.1 hk0f).2
    have hle : ∀ l ∈ F, a l < t → a l ≤ p := fun l hl hlt =>
      Finset.le_max' _ _ (Finset.mem_image_of_mem a (Finset.mem_filter.2 ⟨hl, hlt⟩))
    have hcard : (F.filter (fun l => a l < p)).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨k0, hk0f, ?_⟩
        simp only [Finset.mem_filter, not_and, not_lt]
        exact fun _ => le_of_eq hk0p.symm
      · intro l hl
        simp only [Finset.mem_filter] at hl ⊢
        exact ⟨hl.1, lt_trans hl.2 hpt⟩
    have IH := ih _ hcard p rfl
    have hstep : ∀ s, p < s → s ≤ t →
        Wl F a r s = max 0 (Wl F a r p + Jat F a r p - (s - p)) := fun s hps hst =>
      Wl_step F a r hps k0 hk0F hk0p (fun l hl hls => hle l hl (lt_of_lt_of_le hls hst))
    set m := min t (p + (Wl F a r p + Jat F a r p)) with hm
    have hWp := Wl_nonneg F a r p
    have hJp := Jat_nonneg F a r hr p
    have hpm : p ≤ m := le_min (le_of_lt hpt) (by linarith)
    rw [← measure_inter_add_diff _ (measurableSet_Iio : MeasurableSet (Iio p))]
    have h1 : {s : ℝ | s < t ∧ 0 < Wl F a r s} ∩ Iio p = {s : ℝ | s < p ∧ 0 < Wl F a r s} := by
      ext s
      simp only [mem_inter_iff, mem_setOf_eq, mem_Iio]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨lt_trans h3 hpt, h2⟩, h3⟩
    have h2 : volume ({s : ℝ | s < t ∧ 0 < Wl F a r s} \ Iio p) = ENNReal.ofReal (m - p) := by
      apply le_antisymm
      · rw [← Real.volume_Icc]
        apply measure_mono
        intro s hs
        simp only [mem_diff, mem_setOf_eq, mem_Iio, not_lt] at hs
        obtain ⟨⟨hst, hpos⟩, hps⟩ := hs
        refine ⟨hps, ?_⟩
        rcases lt_or_eq_of_le hps with hps' | hps'
        · rw [hstep s hps' (le_of_lt hst)] at hpos
          have : 0 < Wl F a r p + Jat F a r p - (s - p) := by
            by_contra hc
            push_neg at hc
            rw [max_eq_left hc] at hpos
            exact lt_irrefl _ hpos
          exact le_min (le_of_lt hst) (by linarith)
        · rw [← hps']; exact hpm
      · rw [← Real.volume_Ioo]
        apply measure_mono
        intro s hs
        obtain ⟨hps, hsm⟩ := hs
        have hst : s < t := lt_of_lt_of_le hsm (min_le_left _ _)
        have hsq : s < p + (Wl F a r p + Jat F a r p) := lt_of_lt_of_le hsm (min_le_right _ _)
        simp only [mem_diff, mem_setOf_eq, mem_Iio, not_lt]
        refine ⟨⟨hst, ?_⟩, le_of_lt hps⟩
        rw [hstep s hps (le_of_lt hst)]
        exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    rw [h1, IH, h2, ← ENNReal.ofReal_add (by linarith [Wl_le_Abef F a r hr p]) (by linarith)]
    congr 1
    have hgap : ∀ l ∈ F, a l < t → a l ≤ p := hle
    rw [Abef_split F a r hpt hgap, hstep t hpt le_rfl, hm]
    rcases le_total t (p + (Wl F a r p + Jat F a r p)) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
      ring
  · have hemp : ∀ l ∈ F, ¬ a l < t := fun l hl hlt =>
      hne ⟨l, Finset.mem_filter.2 ⟨hl, hlt⟩⟩
    have hW : ∀ s, s ≤ t → Wl F a r s = 0 := by
      intro s hst
      apply le_antisymm _ (Wl_nonneg F a r s)
      rw [Wl_le_iff]
      exact ⟨le_rfl, fun k hk hks => absurd (lt_of_lt_of_le hks hst) (hemp k hk)⟩
    have hA : Abef F a r t = 0 := by
      unfold Abef
      apply Finset.sum_eq_zero
      intro l hl
      exact absurd (Finset.mem_filter.1 hl).2 (hemp l (Finset.mem_filter.1 hl).1)
    rw [hA, hW t le_rfl, sub_zero, ENNReal.ofReal_zero]
    rw [measure_eq_zero_iff_ae_notMem]
    apply Filter.Eventually.of_forall
    rintro s ⟨hst, hpos⟩
    rw [hW s (le_of_lt hst)] at hpos
    exact lt_irrefl _ hpos

/-! ## D1b: closed workload, monotonicity, stabilization, measurability, served formula -/

/-- closed (right-continuous) workload: includes jobs arriving at `t`. -/
noncomputable def U (F : Finset ι) (a r : ι → ℝ) (t : ℝ) : ℝ := Wl F a r t + Jat F a r t

lemma U_nonneg (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) : 0 ≤ U F a r t :=
  add_nonneg (Wl_nonneg F a r t) (Jat_nonneg F a r hr t)

section mono
variable {F a r}
variable {F' : Finset ι} {T : ℝ}

lemma Ain_mono (h : F ⊆ F') (hr : ∀ l ∈ F', 0 ≤ r l) (x t : ℝ) :
    Ain F a r x t ≤ Ain F' a r x t := by
  unfold Ain
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ h)
  intro l hl _
  exact hr l (Finset.mem_filter.1 hl).1

lemma Jat_mono (h : F ⊆ F') (hr : ∀ l ∈ F', 0 ≤ r l) (t : ℝ) :
    Jat F a r t ≤ Jat F' a r t := by
  unfold Jat
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ h)
  intro l hl _
  exact hr l (Finset.mem_filter.1 hl).1

lemma Wl_mono (h : F ⊆ F') (hr : ∀ l ∈ F', 0 ≤ r l) (t : ℝ) :
    Wl F a r t ≤ Wl F' a r t := by
  rw [Wl_le_iff]
  refine ⟨Wl_nonneg F' a r t, fun k hk hkt => ?_⟩
  have := term_le_Wl F' a r t k (h hk) hkt
  have := Ain_mono (a := a) h hr (a k) t
  linarith

lemma U_mono (h : F ⊆ F') (hr : ∀ l ∈ F', 0 ≤ r l) (t : ℝ) :
    U F a r t ≤ U F' a r t :=
  add_le_add (Wl_mono h hr t) (Jat_mono h hr t)

/-- stabilization: jobs of `F'` outside `F` arrive after `T`, so nothing changes up to `T`. -/
lemma Ain_stab (h : F ⊆ F') (hT : ∀ l ∈ F', l ∉ F → T < a l) {x s : ℝ} (hs : s ≤ T) :
    Ain F a r x s = Ain F' a r x s := by
  unfold Ain
  apply Finset.sum_subset (Finset.filter_subset_filter _ h)
  intro l hl hl'
  rw [Finset.mem_filter] at hl hl'
  have : l ∉ F := fun hF => hl' ⟨hF, hl.2⟩
  exact absurd (lt_trans (hT l hl.1 this) (lt_of_lt_of_le hl.2.2 hs)) (lt_irrefl _)

lemma Jat_stab (h : F ⊆ F') (hT : ∀ l ∈ F', l ∉ F → T < a l) {s : ℝ} (hs : s ≤ T) :
    Jat F a r s = Jat F' a r s := by
  unfold Jat
  apply Finset.sum_subset (Finset.filter_subset_filter _ h)
  intro l hl hl'
  rw [Finset.mem_filter] at hl hl'
  have : l ∉ F := fun hF => hl' ⟨hF, hl.2⟩
  have := hT l hl.1 this
  rw [hl.2] at this
  exact absurd (lt_of_le_of_lt hs this) (lt_irrefl _)

lemma Abef_stab (h : F ⊆ F') (hT : ∀ l ∈ F', l ∉ F → T < a l) {s : ℝ} (hs : s ≤ T) :
    Abef F a r s = Abef F' a r s := by
  unfold Abef
  apply Finset.sum_subset (Finset.filter_subset_filter _ h)
  intro l hl hl'
  rw [Finset.mem_filter] at hl hl'
  have : l ∉ F := fun hF => hl' ⟨hF, hl.2⟩
  exact absurd (lt_trans (hT l hl.1 this) (lt_of_lt_of_le hl.2 hs)) (lt_irrefl _)

lemma Wl_stab (h : F ⊆ F') (hT : ∀ l ∈ F', l ∉ F → T < a l) {s : ℝ} (hs : s ≤ T) :
    Wl F a r s = Wl F' a r s := by
  apply le_antisymm
  · rw [Wl_le_iff]
    refine ⟨Wl_nonneg F' a r s, fun k hk hks => ?_⟩
    rw [Ain_stab h hT hs]
    exact term_le_Wl F' a r s k (h hk) hks
  · rw [Wl_le_iff]
    refine ⟨Wl_nonneg F a r s, fun k hk hks => ?_⟩
    have hkF : k ∈ F := by
      by_contra hc
      exact absurd (lt_trans (hT k hk hc) (lt_of_lt_of_le hks hs)) (lt_irrefl _)
    rw [← Ain_stab h hT hs]
    exact term_le_Wl F a r s k hkF hks

lemma U_stab (h : F ⊆ F') (hT : ∀ l ∈ F', l ∉ F → T < a l) {s : ℝ} (hs : s ≤ T) :
    U F a r s = U F' a r s := by
  unfold U; rw [Wl_stab h hT hs, Jat_stab h hT hs]

end mono

open Classical in
lemma Ain_eq_sum (x t : ℝ) :
    Ain F a r x t = ∑ l ∈ F, (if x ≤ a l ∧ a l < t then r l else 0) := by
  unfold Ain; rw [Finset.sum_filter]

lemma measurable_Ain (x : ℝ) : Measurable (fun t => Ain F a r x t) := by
  classical
  simp_rw [Ain_eq_sum]
  apply Finset.measurable_sum
  intro l _
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hx : x ≤ a l
  · simp only [hx, true_and]
    exact measurableSet_Ioi
  · simp only [hx, false_and, Set.setOf_false]
    exact MeasurableSet.empty

open Classical in
lemma Wl_eq_sup (t : ℝ) :
    Wl F a r t = ((F.sup (fun k => if a k < t then (Ain F a r (a k) t - (t - a k)).toNNReal
      else 0)) : NNReal) := by
  unfold Wl
  congr 1
  rw [Finset.sup_ite]
  simp

lemma measurable_finset_sup {κ : Type*} (G : Finset κ) (g : κ → ℝ → NNReal)
    (hg : ∀ k, Measurable (g k)) : Measurable (fun t => G.sup (fun k => g k t)) := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert k G hk ih =>
    simp_rw [Finset.sup_insert]
    exact (hg k).sup' ih

lemma measurable_Wl : Measurable (fun t => Wl F a r t) := by
  classical
  simp_rw [Wl_eq_sup]
  apply measurable_coe_nnreal_real.comp
  apply measurable_finset_sup
  intro k
  apply Measurable.ite measurableSet_Ioi _ measurable_const
  exact measurable_real_toNNReal.comp ((measurable_Ain F a r (a k)).sub
    (measurable_id.sub measurable_const))

lemma measurable_Jat : Measurable (fun t => Jat F a r t) := by
  classical
  have : (fun t => Jat F a r t) = fun t => ∑ l ∈ F, (if a l = t then r l else 0) := by
    funext t; unfold Jat; rw [Finset.sum_filter]
  rw [this]
  apply Finset.measurable_sum
  intro l _
  exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
    measurable_const

lemma measurable_U : Measurable (fun t => U F a r t) :=
  (measurable_Wl F a r).add (measurable_Jat F a r)

/-- the closed workload has the same busy measure as the left-limit one. -/
lemma busy_eq_U (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) :
    volume {s : ℝ | s < t ∧ 0 < U F a r s} =
      ENNReal.ofReal (Abef F a r t - Wl F a r t) := by
  rw [← busy_eq F a r hr t]
  apply le_antisymm
  · have hsub : {s : ℝ | s < t ∧ 0 < U F a r s} ⊆
        {s : ℝ | s < t ∧ 0 < Wl F a r s} ∪ ((F.image a : Finset ℝ) : Set ℝ) := by
      intro s ⟨hst, hpos⟩
      by_cases hW : 0 < Wl F a r s
      · exact Or.inl ⟨hst, hW⟩
      · right
        have hW0 : Wl F a r s = 0 := le_antisymm (not_lt.1 hW) (Wl_nonneg F a r s)
        unfold U at hpos
        rw [hW0, zero_add] at hpos
        unfold Jat at hpos
        obtain ⟨l, hl, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
        rw [Finset.mem_filter] at hl
        exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨l, hl.1, hl.2⟩)
    calc volume {s : ℝ | s < t ∧ 0 < U F a r s}
        ≤ volume ({s : ℝ | s < t ∧ 0 < Wl F a r s} ∪ ((F.image a : Finset ℝ) : Set ℝ)) :=
          measure_mono hsub
      _ ≤ volume {s : ℝ | s < t ∧ 0 < Wl F a r s} + volume ((F.image a : Finset ℝ) : Set ℝ) :=
          measure_union_le _ _
      _ = volume {s : ℝ | s < t ∧ 0 < Wl F a r s} := by
          rw [(Finset.finite_toSet _).measure_zero, add_zero]
  · apply measure_mono
    intro s ⟨hst, hpos⟩
    exact ⟨hst, lt_of_lt_of_le hpos (le_add_of_nonneg_right (Jat_nonneg F a r hr s))⟩

/-- **served formula**: time in `[.., t)` when the sub-group `F'` is empty but `F` is busy. -/
theorem served_eq {F' : Finset ι} (h : F' ⊆ F) (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) :
    volume {s : ℝ | s < t ∧ U F' a r s = 0 ∧ 0 < U F a r s} =
      ENNReal.ofReal ((Abef F a r t - Wl F a r t) - (Abef F' a r t - Wl F' a r t)) := by
  have hr' : ∀ l ∈ F', 0 ≤ r l := fun l hl => hr l (h hl)
  have hset : {s : ℝ | s < t ∧ U F' a r s = 0 ∧ 0 < U F a r s} =
      {s : ℝ | s < t ∧ 0 < U F a r s} \ {s : ℝ | s < t ∧ 0 < U F' a r s} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_and, not_lt]
    constructor
    · rintro ⟨hst, h0, hp⟩
      exact ⟨⟨hst, hp⟩, fun _ => le_of_eq h0⟩
    · rintro ⟨⟨hst, hp⟩, h0⟩
      exact ⟨hst, le_antisymm (h0 hst) (U_nonneg F' a r hr' s), hp⟩
  have hsub : {s : ℝ | s < t ∧ 0 < U F' a r s} ⊆ {s : ℝ | s < t ∧ 0 < U F a r s} :=
    fun s ⟨hst, hp⟩ => ⟨hst, lt_of_lt_of_le hp (U_mono h hr s)⟩
  have hmeas : MeasurableSet {s : ℝ | s < t ∧ 0 < U F' a r s} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_lt measurable_const (measurable_U F' a r))
  rw [hset, measure_diff hsub hmeas.nullMeasurableSet, busy_eq_U F a r hr t,
    busy_eq_U F' a r hr' t]
  · rw [ENNReal.ofReal_sub (Abef F a r t - Wl F a r t)
      (by linarith [Wl_le_Abef F' a r hr' t] : (0:ℝ) ≤ Abef F' a r t - Wl F' a r t)]
  · rw [busy_eq_U F' a r hr' t]; exact ENNReal.ofReal_ne_top

/-! ## D1c: inserting one job -/

section insert
variable {F a r}

open Classical in
lemma Jat_insert {j : ι} (hj : j ∉ F) (t : ℝ) :
    Jat (insert j F) a r t = Jat F a r t + (if a j = t then r j else 0) := by
  unfold Jat
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (fun hm => hj (Finset.mem_filter.1 hm).1)]; ring
  · rw [add_zero]

open Classical in
lemma Abef_insert {j : ι} (hj : j ∉ F) (t : ℝ) :
    Abef (insert j F) a r t = Abef F a r t + (if a j < t then r j else 0) := by
  unfold Abef
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (fun hm => hj (Finset.mem_filter.1 hm).1)]; ring
  · rw [add_zero]

open Classical in
lemma Ain_insert {j : ι} (hj : j ∉ F) (x t : ℝ) :
    Ain (insert j F) a r x t = Ain F a r x t + (if x ≤ a j ∧ a j < t then r j else 0) := by
  unfold Ain
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (fun hm => hj (Finset.mem_filter.1 hm).1)]; ring
  · rw [add_zero]

lemma Ain_sub_le_Wl {x t : ℝ} (hxt : x ≤ t) : Ain F a r x t - (t - x) ≤ Wl F a r t := by
  classical
  by_cases hne : (F.filter (fun l => x ≤ a l ∧ a l < t)).Nonempty
  · obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image _ a hne
    rw [Finset.mem_filter] at hk
    have hA : Ain F a r x t = Ain F a r (a k) t := by
      unfold Ain
      congr 1
      ext l
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hl, h1, h2⟩
        exact ⟨hl, hmin l (Finset.mem_filter.2 ⟨hl, h1, h2⟩), h2⟩
      · rintro ⟨hl, h1, h2⟩
        exact ⟨hl, le_trans hk.2.1 h1, h2⟩
    have := term_le_Wl F a r t k hk.1 hk.2.2
    rw [hA]
    linarith [hk.2.1]
  · have hA : Ain F a r x t = 0 := by
      unfold Ain
      rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    rw [hA]
    linarith [Wl_nonneg F a r t]

open Classical in
lemma Wl_insert_le {j : ι} (hj : j ∉ F) (hr : ∀ l ∈ insert j F, 0 ≤ r l) (t : ℝ) :
    Wl (insert j F) a r t ≤ Wl F a r t + (if a j < t then r j else 0) := by
  classical
  have hrj : 0 ≤ r j := hr j (Finset.mem_insert_self j F)
  have hite : 0 ≤ (if a j < t then r j else 0) := by split_ifs <;> linarith
  rw [Wl_le_iff]
  refine ⟨add_nonneg (Wl_nonneg F a r t) hite, fun k _ hkt => ?_⟩
  rw [Ain_insert hj]
  have h1 := Ain_sub_le_Wl (F := F) (a := a) (r := r) (le_of_lt hkt)
  have h2 : (if a k ≤ a j ∧ a j < t then r j else 0) ≤ (if a j < t then r j else 0) := by
    split_ifs with h3 h4 h4
    · exact le_rfl
    · exact absurd h3.2 h4
    · exact hrj
    · exact le_rfl
  linarith

lemma U_zero_of_lt {s : ℝ} (h : ∀ l ∈ F, s < a l) : U F a r s = 0 := by
  have hW : Wl F a r s = 0 := by
    apply le_antisymm _ (Wl_nonneg F a r s)
    rw [Wl_le_iff]
    exact ⟨le_rfl, fun k hk hks => absurd (lt_trans (h k hk) hks) (lt_irrefl _)⟩
  have hJ : Jat F a r s = 0 := by
    unfold Jat
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_filter] at hl
    exact absurd (hl.2 ▸ h l hl.1) (lt_irrefl _)
  unfold U; rw [hW, hJ, add_zero]

lemma Wl_empty (t : ℝ) : Wl (∅ : Finset ι) a r t = 0 := by
  unfold Wl; simp

lemma U_empty (t : ℝ) : U (∅ : Finset ι) a r t = 0 := by
  unfold U Jat; rw [Wl_empty]; simp

lemma Wl_le_U (hr : ∀ l ∈ F, 0 ≤ r l) (t : ℝ) : Wl F a r t ≤ U F a r t :=
  le_add_of_nonneg_right (Jat_nonneg F a r hr t)

lemma Jat_le_U (t : ℝ) : Jat F a r t ≤ U F a r t :=
  le_add_of_nonneg_left (Wl_nonneg F a r t)

end insert

/-! ## D2: the generic static-priority schedule -/

section sched
open Classical
set_option linter.unusedSectionVars false

variable {κ : Type*} [LinearOrder κ] (key : ι → κ) (FN : ℕ → Finset ι) (a r : ι → ℝ)

/-- jobs of `FN N` with priority at least that of `j` (including `j`). -/
noncomputable def Le (N : ℕ) (j : ι) : Finset ι := (FN N).filter (fun k => key k ≤ key j)
/-- jobs of `FN N` with priority strictly higher than `j`. -/
noncomputable def Lt (N : ℕ) (j : ι) : Finset ι := (FN N).filter (fun k => key k < key j)

/-- `j` is served at `t` (level `N`): all higher work is done, `j`'s group is busy. -/
def P (N : ℕ) (j : ι) (t : ℝ) : Prop :=
  U (Lt key FN N j) a r t = 0 ∧ 0 < U (Le key FN N j) a r t

def Q (N : ℕ) (j : ι) (t : ℝ) : Prop :=
  P key FN a r N j t ∧ ∀ k ∈ FN N, key k < key j → ¬ P key FN a r N k t

def Ev (j : ι) (t : ℝ) : Prop := ∃ N0, ∀ N ≥ N0, Q key FN a r N j t

noncomputable def Sch (t : ℝ) : Option ι :=
  if h : ∃ j, Ev key FN a r j t then some h.choose else none

/-- `N0` covers time `T`: every job arriving by `T` lies in `FN N0`. -/
def Covers (N0 : ℕ) (T : ℝ) : Prop := ∀ l, a l ≤ T → l ∈ FN N0


variable {key FN a r}

lemma Lt_sub_Le (N : ℕ) (j : ι) : Lt key FN N j ⊆ Le key FN N j := by
  intro k hk
  simp only [Lt, Le, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, le_of_lt hk.2⟩

lemma Le_eq_insert (hkey : Function.Injective key) {N : ℕ} {j : ι} (hj : j ∈ FN N) :
    Le key FN N j = insert j (Lt key FN N j) := by
  ext k
  simp only [Le, Lt, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hk, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inr ⟨hk, h⟩
    · exact Or.inl (hkey h)
  · rintro (rfl | ⟨hk, h⟩)
    · exact ⟨hj, le_rfl⟩
    · exact ⟨hk, le_of_lt h⟩

lemma notmem_Lt (N : ℕ) (j : ι) : j ∉ Lt key FN N j := by
  simp [Lt]

lemma Le_eq_Lt (hkey : Function.Injective key) {N : ℕ} {j : ι} (hj : j ∉ FN N) :
    Le key FN N j = Lt key FN N j := by
  ext k
  simp only [Le, Lt, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact ⟨hk, h⟩
    · exact absurd (hkey h ▸ hk) hj
  · rintro ⟨hk, h⟩; exact ⟨hk, le_of_lt h⟩

lemma P_mem (hkey : Function.Injective key) {N : ℕ} {j : ι} {t : ℝ}
    (h : P key FN a r N j t) : j ∈ FN N := by
  by_contra hj
  have h1 := h.1
  rw [← Le_eq_Lt hkey hj] at h1
  exact absurd h.2 (by rw [h1]; exact lt_irrefl 0)

lemma Q_unique (hkey : Function.Injective key) {N : ℕ} {j j' : ι} {t : ℝ}
    (h : Q key FN a r N j t) (h' : Q key FN a r N j' t) : j = j' := by
  rcases lt_trichotomy (key j) (key j') with hl | he | hl
  · exact absurd h.1 (h'.2 j (P_mem hkey h.1) hl)
  · exact hkey he
  · exact absurd h'.1 (h.2 j' (P_mem hkey h'.1) hl)

lemma Ev_unique (hkey : Function.Injective key) {j j' : ι} {t : ℝ}
    (h : Ev key FN a r j t) (h' : Ev key FN a r j' t) : j = j' := by
  obtain ⟨N1, h1⟩ := h
  obtain ⟨N2, h2⟩ := h'
  exact Q_unique hkey (h1 (max N1 N2) (le_max_left _ _)) (h2 (max N1 N2) (le_max_right _ _))

lemma Sch_eq_some_iff (hkey : Function.Injective key) (j : ι) (t : ℝ) :
    Sch key FN a r t = some j ↔ Ev key FN a r j t := by
  unfold Sch
  constructor
  · intro hS
    split_ifs at hS with h
    · rw [← Option.some_inj.1 hS]; exact h.choose_spec
  · intro hj
    have h : ∃ j, Ev key FN a r j t := ⟨j, hj⟩
    rw [dif_pos h, Ev_unique hkey h.choose_spec hj]

variable (hkey : Function.Injective key) (hFN : Monotone FN)
include hkey hFN

lemma Lt_stab {N0 N : ℕ} {T : ℝ} (hc : Covers FN a N0 T) (hN : N0 ≤ N) (j : ι) :
    ∀ l ∈ Lt key FN N j, l ∉ Lt key FN N0 j → T < a l := by
  intro l hl hl'
  simp only [Lt, Finset.mem_filter] at hl hl'
  by_contra hc'
  exact hl' ⟨hc l (not_lt.1 hc'), hl.2⟩

lemma Le_stab {N0 N : ℕ} {T : ℝ} (hc : Covers FN a N0 T) (hN : N0 ≤ N) (j : ι) :
    ∀ l ∈ Le key FN N j, l ∉ Le key FN N0 j → T < a l := by
  intro l hl hl'
  simp only [Le, Finset.mem_filter] at hl hl'
  by_contra hc'
  exact hl' ⟨hc l (not_lt.1 hc'), hl.2⟩

lemma Lt_mono {N0 N : ℕ} (hN : N0 ≤ N) (j : ι) : Lt key FN N0 j ⊆ Lt key FN N j :=
  Finset.filter_subset_filter _ (hFN hN)

lemma Le_mono {N0 N : ℕ} (hN : N0 ≤ N) (j : ι) : Le key FN N0 j ⊆ Le key FN N j :=
  Finset.filter_subset_filter _ (hFN hN)

lemma P_stab {N0 N : ℕ} {T : ℝ} (hc : Covers FN a N0 T) (hN : N0 ≤ N) (j : ι) {s : ℝ}
    (hs : s ≤ T) : P key FN a r N j s ↔ P key FN a r N0 j s := by
  unfold P
  rw [U_stab (Lt_mono hkey hFN hN j) (Lt_stab hkey hFN hc hN j) hs,
    U_stab (Le_mono hkey hFN hN j) (Le_stab hkey hFN hc hN j) hs]

lemma P_unique (hr : ∀ l, 0 ≤ r l) {N : ℕ} {j j' : ι} {t : ℝ}
    (h : P key FN a r N j t) (h' : P key FN a r N j' t) (hl : key j < key j') : False := by
  have hsub : Le key FN N j ⊆ Lt key FN N j' := by
    intro k hk
    simp only [Le, Lt, Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_le_of_lt hk.2 hl⟩
  have := U_mono (a := a) hsub (fun l _ => hr l) t
  rw [h'.1] at this
  exact absurd h.2 (not_lt.2 this)

lemma Ev_iff (hr : ∀ l, 0 ≤ r l) {N0 : ℕ} {T : ℝ} (hc : Covers FN a N0 T) (j : ι) {s : ℝ}
    (hs : s ≤ T) : Ev key FN a r j s ↔ P key FN a r N0 j s := by
  constructor
  · rintro ⟨M, hM⟩
    have := (hM (max M N0) (le_max_left _ _)).1
    exact (P_stab hkey hFN hc (le_max_right M N0) j hs).1 this
  · intro hP
    refine ⟨N0, fun N hN => ⟨(P_stab hkey hFN hc hN j hs).2 hP, fun k _ hk hPk => ?_⟩⟩
    exact P_unique hkey hFN hr hPk ((P_stab hkey hFN hc hN j hs).2 hP) hk

end sched

/-! ## D2b: served formula and the pathwise schedule clauses -/

section sched2
open Classical
set_option linter.unusedSectionVars false

variable {κ : Type*} [LinearOrder κ] {key : ι → κ} {FN : ℕ → Finset ι} {a r : ι → ℝ}

/-- service received by `j` in `[0, t)` (same shape as the platform's `served`). -/
noncomputable def servedG (S : ℝ → Option ι) (j : ι) (t : ℝ) : ℝ :=
  (volume ({s : ℝ | S s = some j} ∩ Ico 0 t)).toReal

lemma servedG_mono (S : ℝ → Option ι) (j : ι) {t t' : ℝ} (h : t ≤ t') :
    servedG S j t ≤ servedG S j t' := by
  unfold servedG
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  · exact measure_mono (Set.inter_subset_inter_right _ (Set.Ico_subset_Ico_right h))

variable (hkey : Function.Injective key) (hFN : Monotone FN)
  (ha : ∀ l, 0 ≤ a l) (hr : ∀ l, 0 < r l)
include hkey hFN ha hr

lemma served_formula {N0 : ℕ} {t : ℝ} (hc : Covers FN a N0 t) (j : ι) :
    servedG (Sch key FN a r) j t =
      (if a j < t then r j else 0) - (Wl (Le key FN N0 j) a r t - Wl (Lt key FN N0 j) a r t) := by
  have hr0 : ∀ l, 0 ≤ r l := fun l => le_of_lt (hr l)
  have hset : {s : ℝ | Sch key FN a r s = some j} ∩ Ico 0 t =
      {s : ℝ | s < t ∧ U (Lt key FN N0 j) a r s = 0 ∧ 0 < U (Le key FN N0 j) a r s} := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hS, _, hst⟩
      rw [Sch_eq_some_iff hkey, Ev_iff hkey hFN hr0 hc j (le_of_lt hst)] at hS
      exact ⟨hst, hS⟩
    · rintro ⟨hst, hP⟩
      refine ⟨?_, ?_, hst⟩
      · rw [Sch_eq_some_iff hkey, Ev_iff hkey hFN hr0 hc j (le_of_lt hst)]; exact hP
      · by_contra hs
        push_neg at hs
        have := U_zero_of_lt (F := Le key FN N0 j) (r := r)
          (fun l _ => lt_of_lt_of_le hs (ha l))
        rw [this] at hP
        exact lt_irrefl _ hP.2
  unfold servedG
  rw [hset, served_eq _ a r (Lt_sub_Le N0 j) (fun l _ => hr0 l) t]
  by_cases hj : j ∈ FN N0
  · rw [Le_eq_insert hkey hj, Abef_insert (notmem_Lt N0 j)]
    have hle := Wl_insert_le (F := Lt key FN N0 j) (a := a) (notmem_Lt N0 j)
      (fun l _ => hr0 l) t
    have hite : 0 ≤ (if a j < t then r j else 0) := by split_ifs <;> linarith [hr j]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  · rw [Le_eq_Lt hkey hj]
    have hat : ¬ a j < t := fun h => hj (hc j (le_of_lt h))
    rw [if_neg hat, sub_self, sub_self, ENNReal.toReal_ofReal le_rfl]
    ring

lemma Wl_Lt_le_Le (N : ℕ) (j : ι) (t : ℝ) :
    Wl (Lt key FN N j) a r t ≤ Wl (Le key FN N j) a r t :=
  Wl_mono (Lt_sub_Le N j) (fun l _ => le_of_lt (hr l)) t

/-- clause 1: the served job is present. -/
theorem sched_present {t : ℝ} {j : ι} (hcov : ∃ N0, Covers FN a N0 t)
    (hS : Sch key FN a r t = some j) :
    a j ≤ t ∧ servedG (Sch key FN a r) j t < r j := by
  obtain ⟨N0, hc⟩ := hcov
  have hr0 : ∀ l, 0 ≤ r l := fun l => le_of_lt (hr l)
  rw [Sch_eq_some_iff hkey, Ev_iff hkey hFN hr0 hc j le_rfl] at hS
  obtain ⟨hLt, hLe⟩ := hS
  have hajt : a j ≤ t := by
    by_contra hcon
    push_neg at hcon
    have hext : ∀ l ∈ Le key FN N0 j, l ∉ Lt key FN N0 j → t < a l := by
      intro l hl hl'
      simp only [Le, Lt, Finset.mem_filter, not_and, not_lt] at hl hl'
      have : key l = key j := le_antisymm hl.2 (hl' hl.1)
      rw [hkey this]; exact hcon
    rw [← U_stab (Lt_sub_Le N0 j) hext le_rfl, hLt] at hLe
    exact lt_irrefl _ hLe
  refine ⟨hajt, ?_⟩
  rw [served_formula hkey hFN ha hr hc j]
  have hj : j ∈ FN N0 := hc j hajt
  rcases lt_or_eq_of_le hajt with hlt | heq
  · rw [if_pos hlt]
    have hWLt : Wl (Lt key FN N0 j) a r t = 0 :=
      le_antisymm (hLt ▸ Wl_le_U (fun l _ => hr0 l) t) (Wl_nonneg _ a r t)
    have hJLt : Jat (Lt key FN N0 j) a r t = 0 :=
      le_antisymm (hLt ▸ Jat_le_U t) (Jat_nonneg _ a r (fun l _ => hr0 l) t)
    have hJLe : Jat (Le key FN N0 j) a r t = 0 := by
      rw [Le_eq_insert hkey hj, Jat_insert (notmem_Lt N0 j), hJLt, if_neg (ne_of_lt hlt)]
      ring
    have : 0 < Wl (Le key FN N0 j) a r t := by
      unfold U at hLe; rw [hJLe, add_zero] at hLe; exact hLe
    linarith
  · rw [if_neg (by rw [heq]; exact lt_irrefl t)]
    linarith [Wl_Lt_le_Le hkey hFN ha hr (a := a) (r := r) (key := key) (FN := FN) N0 j t, hr j]

/-- static priority: the served job has the least key among present jobs. -/
theorem sched_prio {t : ℝ} {j j' : ι} (hcov : ∃ N0, Covers FN a N0 t)
    (hS : Sch key FN a r t = some j) (haj' : a j' ≤ t)
    (hsv : servedG (Sch key FN a r) j' t < r j') : key j ≤ key j' := by
  obtain ⟨N0, hc⟩ := hcov
  have hr0 : ∀ l, 0 ≤ r l := fun l => le_of_lt (hr l)
  rw [Sch_eq_some_iff hkey, Ev_iff hkey hFN hr0 hc j le_rfl] at hS
  by_contra hlt
  push_neg at hlt
  have hsub : Le key FN N0 j' ⊆ Lt key FN N0 j := by
    intro k hk
    simp only [Le, Lt, Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_le_of_lt hk.2 hlt⟩
  have hU : U (Le key FN N0 j') a r t = 0 :=
    le_antisymm (hS.1 ▸ U_mono hsub (fun l _ => hr0 l) t) (U_nonneg _ a r (fun l _ => hr0 l) t)
  have hW : Wl (Le key FN N0 j') a r t = 0 :=
    le_antisymm (hU ▸ Wl_le_U (fun l _ => hr0 l) t) (Wl_nonneg _ a r t)
  have hj' : j' ∈ FN N0 := hc j' haj'
  rw [served_formula hkey hFN ha hr hc j'] at hsv
  rcases lt_or_eq_of_le haj' with hl | he
  · rw [if_pos hl, hW] at hsv
    have := Wl_nonneg (Lt key FN N0 j') a r t
    have := Wl_Lt_le_Le hkey hFN ha hr (a := a) (r := r) (key := key) (FN := FN) N0 j' t
    linarith
  · have hJ : r j' ≤ Jat (Le key FN N0 j') a r t := by
      rw [Le_eq_insert hkey hj', Jat_insert (notmem_Lt N0 j'), if_pos he]
      linarith [Jat_nonneg (Lt key FN N0 j') a r (fun l _ => hr0 l) t]
    have := Jat_le_U (F := Le key FN N0 j') (a := a) (r := r) t
    linarith [hr j']

/-- non-idling: if nothing is served, every arrived job is finished. -/
theorem sched_none {t : ℝ} {j' : ι} (hcov : ∃ N0, Covers FN a N0 t)
    (hS : Sch key FN a r t = none) (haj' : a j' ≤ t) :
    r j' ≤ servedG (Sch key FN a r) j' t := by
  obtain ⟨N0, hc⟩ := hcov
  have hr0 : ∀ l, 0 ≤ r l := fun l => le_of_lt (hr l)
  by_contra hsv
  push_neg at hsv
  have hj' : j' ∈ FN N0 := hc j' haj'
  have hpos : 0 < U (Le key FN N0 j') a r t := by
    rw [served_formula hkey hFN ha hr hc j'] at hsv
    rcases lt_or_eq_of_le haj' with hl | he
    · rw [if_pos hl] at hsv
      have := Wl_nonneg (Lt key FN N0 j') a r t
      have := Wl_le_U (F := Le key FN N0 j') (a := a) (r := r) (fun l _ => hr0 l) t
      linarith
    · have hJ : r j' ≤ Jat (Le key FN N0 j') a r t := by
        rw [Le_eq_insert hkey hj', Jat_insert (notmem_Lt N0 j'), if_pos he]
        linarith [Jat_nonneg (Lt key FN N0 j') a r (fun l _ => hr0 l) t]
      have := Jat_le_U (F := Le key FN N0 j') (a := a) (r := r) t
      linarith [hr j']
  have hne : ((FN N0).filter (fun k => 0 < U (Le key FN N0 k) a r t)).Nonempty :=
    ⟨j', Finset.mem_filter.2 ⟨hj', hpos⟩⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image _ key hne
  rw [Finset.mem_filter] at hk
  have hLt : U (Lt key FN N0 k) a r t = 0 := by
    by_cases hne' : (Lt key FN N0 k).Nonempty
    · obtain ⟨k', hk', hmax⟩ := Finset.exists_max_image _ key hne'
      have hk'F : k' ∈ FN N0 := (Finset.mem_filter.1 hk').1
      have hk'lt : key k' < key k := (Finset.mem_filter.1 hk').2
      have hsub : Lt key FN N0 k ⊆ Le key FN N0 k' := by
        intro m hm
        simp only [Le, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.1 hm).1, hmax m hm⟩
      have hk'0 : U (Le key FN N0 k') a r t ≤ 0 := by
        by_contra hc'
        push_neg at hc'
        have := hmin k' (Finset.mem_filter.2 ⟨hk'F, hc'⟩)
        exact absurd hk'lt (not_lt.2 this)
      exact le_antisymm (le_trans (U_mono hsub (fun l _ => hr0 l) t) hk'0)
        (U_nonneg _ a r (fun l _ => hr0 l) t)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne', U_empty]
  have hEv : Ev key FN a r k t := (Ev_iff hkey hFN hr0 hc k le_rfl).2 ⟨hLt, hk.2⟩
  rw [← Sch_eq_some_iff hkey] at hEv
  rw [hS] at hEv
  simp at hEv

/-- busy-period start: if the system is empty just before `a0`, every earlier job is done. -/
theorem sched_bp {a0 : ℝ} (hcov : ∃ N0, Covers FN a N0 a0)
    (hBP : ∀ G : Finset ι, ∀ x ≤ a0, Ain G a r x a0 ≤ a0 - x) {k : ι} (hk : a k < a0)
    {t : ℝ} (ht : a0 ≤ t) : r k ≤ servedG (Sch key FN a r) k t := by
  obtain ⟨N0, hc⟩ := hcov
  have hW : ∀ G : Finset ι, Wl G a r a0 = 0 := by
    intro G
    apply le_antisymm _ (Wl_nonneg G a r a0)
    rw [Wl_le_iff]
    exact ⟨le_rfl, fun m _ hm => by linarith [hBP G (a m) (le_of_lt hm)]⟩
  have h0 : servedG (Sch key FN a r) k a0 = r k := by
    rw [served_formula hkey hFN ha hr hc k, if_pos hk, hW, hW]; ring
  rw [← h0]
  exact servedG_mono _ k ht

end sched2

/-! ## D3: joint measurability in (parameter, time) -/

section joint
open Classical
set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] (F : Finset ι) (A R : Ω → ι → ℝ)
  (hA : ∀ l, Measurable (fun x => A x l)) (hR : ∀ l, Measurable (fun x => R x l))
include hA hR

lemma measurable_Ain2 (X : Ω × ℝ → ℝ) (hX : Measurable X) :
    Measurable (fun p : Ω × ℝ => Ain F (A p.1) (R p.1) (X p) p.2) := by
  simp_rw [Ain_eq_sum]
  apply Finset.measurable_sum
  intro l _
  apply Measurable.ite _ ((hR l).comp measurable_fst) measurable_const
  rw [Set.setOf_and]
  exact (measurableSet_le hX ((hA l).comp measurable_fst)).inter
    (measurableSet_lt ((hA l).comp measurable_fst) measurable_snd)

omit hA hR in
lemma measurable_finset_sup2 {κ' β : Type*} [MeasurableSpace β] (G : Finset κ')
    (g : κ' → β → NNReal) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun t => G.sup (fun k => g k t)) := by
  induction G using Finset.induction_on with
  | empty => simp
  | insert k G hk ih =>
    simp_rw [Finset.sup_insert]
    exact (hg k).sup' ih

lemma measurable_Wl2 : Measurable (fun p : Ω × ℝ => Wl F (A p.1) (R p.1) p.2) := by
  simp_rw [Wl_eq_sup]
  apply measurable_coe_nnreal_real.comp
  apply measurable_finset_sup2
  intro k
  apply Measurable.ite (measurableSet_lt ((hA k).comp measurable_fst) measurable_snd) _
    measurable_const
  exact measurable_real_toNNReal.comp
    ((measurable_Ain2 F A R hA hR _ ((hA k).comp measurable_fst)).sub
      (measurable_snd.sub ((hA k).comp measurable_fst)))

lemma measurable_Jat2 : Measurable (fun p : Ω × ℝ => Jat F (A p.1) (R p.1) p.2) := by
  have : (fun p : Ω × ℝ => Jat F (A p.1) (R p.1) p.2) =
      fun p => ∑ l ∈ F, (if A p.1 l = p.2 then R p.1 l else 0) := by
    funext p; unfold Jat; rw [Finset.sum_filter]
  rw [this]
  apply Finset.measurable_sum
  intro l _
  exact Measurable.ite (measurableSet_eq_fun ((hA l).comp measurable_fst) measurable_snd)
    ((hR l).comp measurable_fst) measurable_const

lemma measurable_U2 : Measurable (fun p : Ω × ℝ => U F (A p.1) (R p.1) p.2) :=
  (measurable_Wl2 F A R hA hR).add (measurable_Jat2 F A R hA hR)

omit hA hR in
variable {κ : Type*} [LinearOrder κ] (key : ι → κ) (FN : ℕ → Finset ι) in
lemma measurableSet_P (N : ℕ) (j : ι) (hA : ∀ l, Measurable (fun x => A x l))
    (hR : ∀ l, Measurable (fun x => R x l)) :
    MeasurableSet {p : Ω × ℝ | P key FN (A p.1) (R p.1) N j p.2} := by
  unfold P
  rw [Set.setOf_and]
  exact (measurableSet_eq_fun (measurable_U2 _ A R hA hR) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_U2 _ A R hA hR))

omit hA hR in
variable {κ : Type*} [LinearOrder κ] (key : ι → κ) (FN : ℕ → Finset ι) in
/-- clause 1 generic: the schedule's level sets are jointly measurable. -/
theorem measurableSet_Sch (hkey : Function.Injective key) (j : ι)
    (hA : ∀ l, Measurable (fun x => A x l)) (hR : ∀ l, Measurable (fun x => R x l)) :
    MeasurableSet {p : Ω × ℝ | Sch key FN (A p.1) (R p.1) p.2 = some j} := by
  have hset : {p : Ω × ℝ | Sch key FN (A p.1) (R p.1) p.2 = some j} =
      ⋃ N0 : ℕ, ⋂ N : ℕ, ⋂ (_ : N0 ≤ N),
        ({p : Ω × ℝ | P key FN (A p.1) (R p.1) N j p.2} ∩
          ⋂ k ∈ (FN N).filter (fun k => key k < key j),
            {p : Ω × ℝ | P key FN (A p.1) (R p.1) N k p.2}ᶜ) := by
    ext p
    simp only [Set.mem_setOf_eq, Sch_eq_some_iff hkey, Ev, Q, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_inter_iff, Finset.mem_filter, Set.mem_compl_iff, ge_iff_le]
    constructor
    · rintro ⟨N0, h⟩
      exact ⟨N0, fun N hN => ⟨(h N hN).1, fun k hk => (h N hN).2 k hk.1 hk.2⟩⟩
    · rintro ⟨N0, h⟩
      exact ⟨N0, fun N hN => ⟨(h N hN).1, fun k hk hkj => (h N hN).2 k ⟨hk, hkj⟩⟩⟩
  rw [hset]
  refine MeasurableSet.iUnion fun N0 => MeasurableSet.iInter fun N =>
    MeasurableSet.iInter fun _ => ?_
  refine (measurableSet_P A R key FN N j hA hR).inter ?_
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun k _ => ?_
  exact (measurableSet_P A R key FN N k hA hR).compl

end joint

/-! ## P1c: the workload empties after any time when the arrived work has negative drift -/

section empty
open Finset

lemma Ain_eq_Abef_sub {x t : ℝ} (hxt : x ≤ t) :
    Ain F a r x t = Abef F a r t - Abef F a r x := by
  unfold Ain Abef
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h1 : x ≤ a l ∧ a l < t
  · rw [if_pos h1, if_pos h1.2, if_neg (not_lt.2 h1.1)]; ring
  · rw [if_neg h1]
    by_cases h2 : a l < t
    · have h3 : a l < x := by
        by_contra h3; exact h1 ⟨not_lt.1 h3, h2⟩
      rw [if_pos h2, if_pos h3]; ring
    · have h3 : ¬ a l < x := fun h3 => h2 (lt_of_lt_of_le h3 hxt)
      rw [if_neg h2, if_neg h3]; ring

theorem exists_Wl_zero (hr : ∀ l ∈ F, 0 ≤ r l) (t0 T : ℝ) (hT : Abef F a r T - T < -t0) :
    ∃ t, t0 < t ∧ t ≤ T ∧ Wl F a r t = 0 := by
  classical
  set f : ℝ → ℝ := fun s => Abef F a r s - s with hf
  set E : Finset ℝ := insert T ((F.filter (fun k => a k ≤ T)).image a) with hE
  obtain ⟨t, htE, hmin⟩ := E.exists_min_image f ⟨T, mem_insert_self _ _⟩
  have htT : t ≤ T := by
    rcases mem_insert.1 htE with h | h
    · exact h.le
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h
      exact (mem_filter.1 hk).2
  have hA0 : ∀ s, 0 ≤ Abef F a r s := fun s =>
    sum_nonneg fun l hl => hr l (mem_filter.1 hl).1
  have hft : f t ≤ f T := hmin T (mem_insert_self _ _)
  refine ⟨t, ?_, htT, ?_⟩
  · have := hA0 t
    simp only [hf] at hft
    linarith
  · apply le_antisymm _ (Wl_nonneg F a r t)
    rw [Wl_le_iff]
    refine ⟨le_rfl, fun k hk hkt => ?_⟩
    have hkE : a k ∈ E :=
      mem_insert_of_mem (mem_image.2 ⟨k, mem_filter.2 ⟨hk, le_trans hkt.le htT⟩, rfl⟩)
    have := hmin _ hkE
    rw [Ain_eq_Abef_sub F a r hkt.le]
    simp only [hf] at this
    linarith

end empty

end CMQ


/-! ## P1c (deterministic): stability `ρ < 1` + per-class SLLN limits ⇒ the work arrived before `T`
minus `T` tends to `-∞`, uniformly in the truncation. Mathlib only (laptop iteration). -/

namespace CMS
open Filter Finset Topology

/-- eventually-linear upper bound for partial sums turned into a bound valid for all `n`. -/
lemma sum_le_lin {s : ℕ → ℝ} (hs0 : ∀ m, 0 ≤ s m) {β : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, (∑ m ∈ range n, s m) / n < β) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ m ∈ range n, s m ≤ n * β + C := by
  obtain ⟨n1, hn1⟩ := (h.and (eventually_gt_atTop 0)).exists_forall_of_atTop
  refine ⟨∑ m ∈ range n1, s m + |β| * n1, fun n => ?_⟩
  by_cases hn : n1 ≤ n
  · obtain ⟨h1, h2⟩ := hn1 n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h2
    have := (div_lt_iff₀ hnpos).1 h1
    have : 0 ≤ ∑ m ∈ range n1, s m + |β| * n1 :=
      add_nonneg (sum_nonneg fun m _ => hs0 m) (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    nlinarith
  · push_neg at hn
    have h1 : ∑ m ∈ range n, s m ≤ ∑ m ∈ range n1, s m :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn.le) fun m _ _ => hs0 m
    have h2 : -(|β| * n1) ≤ n * β := by
      have : (n : ℝ) ≤ n1 := by exact_mod_cast hn.le
      have hb := neg_abs_le β
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith [abs_nonneg β]
    linarith

/-- eventually-linear lower bound for partial sums: indices with partial sum below `T` are few. -/
lemma idx_bound {x : ℕ → ℝ} (hx0 : ∀ m, 0 ≤ x m) {α : ℝ} (hα : 0 < α)
    (h : ∀ᶠ n : ℕ in atTop, α < (∑ m ∈ range n, x m) / n) :
    ∃ n0 : ℕ, ∀ T : ℝ, ∀ n : ℕ, ∑ m ∈ range (n + 1), x m < T → (n : ℝ) + 1 ≤ n0 + T / α := by
  obtain ⟨n0, hn0⟩ := (h.and (eventually_gt_atTop 0)).exists_forall_of_atTop
  refine ⟨n0, fun T n hT => ?_⟩
  have hS : 0 ≤ ∑ m ∈ range (n + 1), x m := sum_nonneg fun m _ => hx0 m
  have hTa : 0 ≤ T / α := div_nonneg (by linarith) hα.le
  by_cases hn : n0 ≤ n + 1
  · obtain ⟨h1, h2⟩ := hn0 (n + 1) hn
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h2
    have h3 := (lt_div_iff₀ hnpos).1 h1
    push_cast at h3
    have h4 : (n + 1 : ℝ) * α < T := by linarith
    have h5 : (n : ℝ) + 1 < T / α := by rw [lt_div_iff₀ hα]; linarith
    have : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
    linarith
  · push_neg at hn
    have : ((n + 1 : ℕ) : ℝ) ≤ n0 := by exact_mod_cast hn.le
    push_cast at this
    linarith

/-- one class: work of the arrivals before `T` (any truncation `B`) is at most linear in `T`. -/
lemma class_bound {x s : ℕ → ℝ} (hs0 : ∀ m, 0 ≤ s m) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (n0 : ℕ) (hn0 : ∀ T : ℝ, ∀ n : ℕ, ∑ m ∈ range (n + 1), x m < T → (n : ℝ) + 1 ≤ n0 + T / α)
    (C : ℝ) (hC : ∀ n : ℕ, ∑ m ∈ range n, s m ≤ n * β + C) (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    ∑ n ∈ (range B).filter (fun n => ∑ m ∈ range (n + 1), x m < T), s n ≤
      T * (β / α) + ((n0 + 1) * β + C) := by
  set P := n0 + ⌈T / α⌉₊ with hP
  have hsub : (range B).filter (fun n => ∑ m ∈ range (n + 1), x m < T) ⊆ range P := by
    intro n hn
    rw [mem_filter] at hn
    have h1 := hn0 T n hn.2
    have hc := Nat.le_ceil (T / α)
    rw [Finset.mem_range]
    have : (n : ℝ) < (P : ℝ) := by rw [hP]; push_cast; linarith
    exact_mod_cast this
  have hc := Nat.ceil_lt_add_one (div_nonneg hT hα.le)
  calc ∑ n ∈ (range B).filter (fun n => ∑ m ∈ range (n + 1), x m < T), s n
      ≤ ∑ n ∈ range P, s n := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hs0 _
    _ ≤ P * β + C := hC P
    _ ≤ T * (β / α) + ((n0 + 1) * β + C) := by
        rw [hP]; push_cast
        have h1 : (⌈T / α⌉₊ : ℝ) * β ≤ (T / α + 1) * β := mul_le_mul_of_nonneg_right hc.le hβ.le
        have h2 : T / α * β = T * (β / α) := by ring
        nlinarith

/-- stability: arrived work before `T` minus `T` is eventually below any level, uniformly in `B`. -/
theorem drift {K : Type*} [Fintype K] (lam mu : K → ℝ) (hl : ∀ k, 0 < lam k)
    (hm : ∀ k, 0 < mu k) (hρ : ∑ k, lam k / mu k < 1) (x s : K → ℕ → ℝ)
    (hx0 : ∀ k m, 0 ≤ x k m) (hs0 : ∀ k m, 0 ≤ s k m)
    (hx : ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, x k m) / n) atTop (𝓝 (1 / lam k)))
    (hs : ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, s k m) / n) atTop (𝓝 (1 / mu k))) :
    ∀ c : ℝ, ∃ T : ℝ, 0 ≤ T ∧ ∀ B : ℕ,
      (∑ k, ∑ n ∈ (range B).filter (fun n => ∑ m ∈ range (n + 1), x k m < T), s k n) - T < c := by
  have hcont : Tendsto (fun ε : ℝ => ∑ k, (1 / mu k + ε) / (1 / lam k - ε)) (𝓝 0)
      (𝓝 (∑ k, lam k / mu k)) := by
    apply tendsto_finset_sum
    intro k _
    have hc : ContinuousAt (fun ε : ℝ => (1 / mu k + ε) / (1 / lam k - ε)) 0 := by
      apply ContinuousAt.div <;> first | fun_prop | simp [(hl k).ne']
    have he : (1 / mu k + 0) / (1 / lam k - 0) = lam k / mu k := by
      have := (hl k).ne'; have := (hm k).ne'; field_simp; ring
    rw [← he]
    exact hc.tendsto
  have e1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∑ k, (1 / mu k + ε) / (1 / lam k - ε) < 1 :=
    hcont.eventually (gt_mem_nhds hρ)
  have e2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ k, ε < 1 / lam k / 2 :=
    eventually_all.2 fun k => gt_mem_nhds (half_pos (one_div_pos.2 (hl k)))
  obtain ⟨ε, ⟨hsum, hsmall⟩, hε⟩ :=
    (((e1.and e2).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).and
      self_mem_nhdsWithin).exists
  have hε : 0 < ε := hε
  set α : K → ℝ := fun k => 1 / lam k - ε with hαdef
  set β : K → ℝ := fun k => 1 / mu k + ε with hβdef
  have hα : ∀ k, 0 < α k := fun k => by
    have := hsmall k; have := one_div_pos.2 (hl k); simp only [hαdef]; linarith
  have hβ : ∀ k, 0 < β k := fun k => by
    have := one_div_pos.2 (hm k); simp only [hβdef]; linarith
  have hn0 : ∀ k, ∃ n0 : ℕ, ∀ T : ℝ, ∀ n : ℕ,
      ∑ m ∈ range (n + 1), x k m < T → (n : ℝ) + 1 ≤ n0 + T / α k := fun k =>
    idx_bound (hx0 k) (hα k) ((tendsto_order.1 (hx k)).1 _ (by simp only [hαdef]; linarith))
  have hC : ∀ k, ∃ C : ℝ, ∀ n : ℕ, ∑ m ∈ range n, s k m ≤ n * β k + C := fun k =>
    sum_le_lin (hs0 k) ((tendsto_order.1 (hs k)).2 _ (by simp only [hβdef]; linarith))
  choose n0 hn0 using hn0
  choose C hC using hC
  set ρ' := ∑ k, β k / α k with hρ'
  have hρ'1 : ρ' < 1 := hsum
  set K0 := ∑ k, ((n0 k + 1) * β k + C k) with hK0
  intro c
  refine ⟨max 0 ((K0 - c) / (1 - ρ') + 1), le_max_left _ _, fun B => ?_⟩
  set T := max 0 ((K0 - c) / (1 - ρ') + 1) with hT
  have hT0 : 0 ≤ T := le_max_left _ _
  have hb : ∀ k, ∑ n ∈ (range B).filter (fun n => ∑ m ∈ range (n + 1), x k m < T), s k n ≤
      T * (β k / α k) + ((n0 k + 1) * β k + C k) := fun k =>
    class_bound (hs0 k) (hα k) (hβ k) (n0 k) (hn0 k) (C k) (hC k) T hT0 B
  have hA := sum_le_sum fun k (_ : k ∈ (univ : Finset K)) => hb k
  rw [sum_add_distrib, ← mul_sum] at hA
  have h1 : (K0 - c) / (1 - ρ') < T := by
    have := le_max_right 0 ((K0 - c) / (1 - ρ') + 1); rw [← hT] at this; linarith
  have h2 : K0 - c < T * (1 - ρ') := by rwa [div_lt_iff₀ (by linarith)] at h1
  have : ∑ k, ∑ n ∈ (range B).filter (fun n => ∑ m ∈ range (n + 1), x k m < T), s k n ≤
      T * ρ' + K0 := hA
  nlinarith

end CMS

/-! ## mean of the exponential law -/
namespace CMS
open MeasureTheory ProbabilityTheory Set

lemma gpdf_mul_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (gammaPDF 1 r x).toReal • x =
      (Ioi (0 : ℝ)).indicator (fun t => r * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) x := by
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), gammaPDF_of_nonneg hx.le,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num [Real.Gamma_one]
    ring
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    rcases (not_lt.1 hx).lt_or_eq with h | h
    · rw [gammaPDF_of_neg h]; simp
    · rw [h]; simp

theorem expMeasure_mean {r : ℝ} (hr : 0 < r) :
    Integrable id (expMeasure r) ∧ ∫ x, x ∂(expMeasure r) = 1 / r := by
  have hm : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 r x < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hI : ∫ t in Ioi (0 : ℝ), r * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t))) = 1 / r := by
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hr, Real.Gamma_two,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hint : IntegrableOn (fun t => r * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hI]; positivity)
  constructor
  · show Integrable id (volume.withDensity (gammaPDF 1 r))
    rw [integrable_withDensity_iff_integrable_smul' hm hlt]
    simp_rw [id, gpdf_mul_eq hr]
    exact (integrable_indicator_iff measurableSet_Ioi).2 hint
  · show ∫ x, x ∂(volume.withDensity (gammaPDF 1 r)) = 1 / r
    rw [integral_withDensity_eq_integral_toReal_smul hm hlt]
    simp_rw [gpdf_mul_eq hr]
    rw [integral_indicator measurableSet_Ioi]
    exact hI

end CMS

/-! ## SLLN for each class stream of a product of exponentials -/
namespace CMS
open MeasureTheory ProbabilityTheory Filter Finset Topology

theorem ae_slln_infinitePi {M : ℕ} (rate : Fin M → ℝ) (hrate : ∀ i, 0 < rate i) :
    haveI : ∀ j : Fin M × ℕ, IsProbabilityMeasure (expMeasure (rate j.1)) :=
      fun j => isProbabilityMeasure_expMeasure (hrate j.1)
    ∀ᵐ x ∂(Measure.infinitePi (fun j : Fin M × ℕ => expMeasure (rate j.1))),
      ∀ k : Fin M, Tendsto (fun n : ℕ => (∑ m ∈ range n, (x (k, m) : ℝ)) / (n : ℝ)) atTop
        (𝓝 (1 / rate k)) := by
  haveI : ∀ j : Fin M × ℕ, IsProbabilityMeasure (expMeasure (rate j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (hrate j.1)
  set μ0 := Measure.infinitePi (fun j : Fin M × ℕ => expMeasure (rate j.1))
  rw [ae_all_iff]
  intro k
  have hind0 : iIndepFun (fun (j : Fin M × ℕ) (x : Fin M × ℕ → ℝ) => x j) μ0 :=
    iIndepFun_infinitePi (X := fun _ y => y) (fun _ => measurable_id)
  have hind : iIndepFun (fun (n : ℕ) (x : Fin M × ℕ → ℝ) => x (k, n)) μ0 :=
    hind0.precomp (g := fun n : ℕ => (k, n)) (fun a b h => by simpa using h)
  have hid : ∀ n, IdentDistrib (fun x : Fin M × ℕ → ℝ => x (k, n)) (fun x => x (k, 0)) μ0 μ0 :=
    fun n => ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable, by
      rw [(measurePreserving_eval_infinitePi _ (k, n)).map_eq,
        (measurePreserving_eval_infinitePi _ (k, 0)).map_eq]⟩
  have hmap := (measurePreserving_eval_infinitePi
    (fun j : Fin M × ℕ => expMeasure (rate j.1)) (k, 0)).map_eq
  have hint : Integrable (fun x : Fin M × ℕ → ℝ => x (k, 0)) μ0 := by
    have h := (expMeasure_mean (hrate k)).1
    rw [← hmap] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_pi_apply _).aemeasurable).1 h
  have hmean : ∫ x, x (k, 0) ∂μ0 = 1 / rate k := by
    have h := integral_map (μ := μ0) (φ := Function.eval (k, 0)) (f := fun y : ℝ => y)
      (measurable_pi_apply (k, 0)).aemeasurable measurable_id.aestronglyMeasurable
    rw [← (expMeasure_mean (hrate k)).2, ← hmap]
    exact h.symm
  have h := strong_law_ae_real (fun n (x : Fin M × ℕ → ℝ) => x (k, n)) hint
    (fun i j hij => hind.indepFun hij) hid
  rw [hmean] at h
  exact h

end CMS


/-! ## P2a: Poisson restart at a deterministic time for one i.i.d. exponential stream.
Mathlib only (laptop iteration). `x : ℕ → ℝ` are i.i.d. `Exp r` interarrival times, arrival `m`
happens at `psum x (m+1)`. On the event `Ev t k x` (exactly `k` arrivals in `[0, t]`) the
restarted stream is `postK t k x` (residual time, then the later interarrivals). -/

namespace CMR
open MeasureTheory ProbabilityTheory Set

/-- prepend an element to a sequence -/
def consN {α : Type*} (a : α) (f : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => f n

@[simp] lemma consN_zero {α : Type*} (a : α) (f : ℕ → α) : consN a f 0 = a := rfl
@[simp] lemma consN_succ {α : Type*} (a : α) (f : ℕ → α) (n : ℕ) : consN a f (n + 1) = f n := rfl

lemma measurable_consN {α : Type*} [MeasurableSpace α] :
    Measurable (fun p : α × (ℕ → α) => consN p.1 p.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

lemma prod_split_zero {M : Type*} [CommMonoid M] (s : Finset ℕ) (g : ℕ → M) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1) := by
  classical
  have key : ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1)
      = ∏ i ∈ s.erase 0, g i := by
    refine Finset.prod_nbij' (fun n => n + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_preimage] at hn
      simp [hn]
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_erase] at hi
      simp only [Finset.mem_coe, Finset.mem_preimage]
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi.1)]; exact hi.2
    · intro n _; simp
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_erase] at hi
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi.1)
    · intro n _; rfl
  rw [key]
  by_cases h0 : 0 ∈ s
  · rw [if_pos h0, Finset.mul_prod_erase s g h0]
  · rw [if_neg h0, one_mul, Finset.erase_eq_of_notMem h0]

/-- the i.i.d. product measure splits off its first coordinate. -/
theorem map_consN {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi fun _ : ℕ => ν)).map (fun p : α × (ℕ → α) => consN p.1 p.2)
      = Measure.infinitePi fun _ : ℕ => ν := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply measurable_consN (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : α × (ℕ → α) => consN p.1 p.2) ⁻¹' (Set.pi ↑s t) =
      (if 0 ∈ s then t 0 else univ) ×ˢ
        Set.pi ↑(s.preimage Nat.succ Nat.succ_injective.injOn) (fun n => t (n + 1)) := by
    ext ⟨a, f⟩
    simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun n hn => h (n + 1) hn⟩
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa [hi] using h0
      | succ n => exact h1 n hi
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht (i + 1)), prod_split_zero s]
  congr 1
  split_ifs <;> simp

lemma gammaPDF_one_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    gammaPDF 1 r x = ENNReal.ofReal (r * Real.exp (-(r * x))) := by
  rw [gammaPDF_of_nonneg hx]
  congr 1
  simp [Real.Gamma_one]

/-- memorylessness of the exponential law, integrated form. -/
theorem expMeasure_memoryless {r : ℝ} {t : ℝ} (ht : 0 ≤ t) {h : ℝ → ENNReal}
    (hh : Measurable h) :
    ∫⁻ a, (Ioi t).indicator (fun a => h (a - t)) a ∂(expMeasure r)
      = ENNReal.ofReal (Real.exp (-(r * t))) * ∫⁻ a, h a ∂(expMeasure r) := by
  have hm : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hmi : Measurable ((Ioi t).indicator (fun a => h (a - t))) :=
    (hh.comp (measurable_id.sub_const t)).indicator measurableSet_Ioi
  show ∫⁻ a, _ ∂(volume.withDensity (gammaPDF 1 r)) =
    _ * ∫⁻ a, h a ∂(volume.withDensity (gammaPDF 1 r))
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hmi,
    lintegral_withDensity_eq_lintegral_mul _ hm hh, ← lintegral_const_mul _ (hm.mul hh)]
  conv_lhs => rw [← lintegral_add_right_eq_self _ t]
  have hne : ∀ᵐ b ∂(volume : Measure ℝ), b ≠ 0 := by
    rw [ae_iff]; simp
  refine lintegral_congr_ae ?_
  filter_upwards [hne] with b hb
  simp only [Pi.mul_apply]
  rcases hb.lt_or_gt with hb0 | hb0
  · rw [indicator_of_notMem (show b + t ∉ Ioi t by simp; linarith), gammaPDF_of_neg hb0]
    simp
  · rw [indicator_of_mem (show b + t ∈ Ioi t by simp; linarith), add_sub_cancel_right,
      gammaPDF_one_of_nonneg (by linarith : 0 ≤ b + t), gammaPDF_one_of_nonneg hb0.le,
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 2
    rw [show -(r * (b + t)) = -(r * t) + -(r * b) by ring, Real.exp_add]
    ring

/-! ### the restarted stream -/

/-- `psum x k = x 0 + ⋯ + x (k-1)`; arrival `m` happens at `psum x (m+1)`. -/
def psum (x : ℕ → ℝ) (k : ℕ) : ℝ := ∑ m ∈ Finset.range k, x m

/-- exactly the arrivals `0, …, k-1` happen in `[0, t]`. -/
def Ev (t : ℝ) (k : ℕ) (x : ℕ → ℝ) : Prop := (∀ j < k, psum x (j + 1) ≤ t) ∧ t < psum x (k + 1)

/-- the stream restarted at time `t` on the event `Ev t k`. -/
noncomputable def postK (t : ℝ) (k : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j = 0 then psum x (k + 1) - t else x (k + j)

/-- the first `k` interarrival times. -/
def preK {α : Type*} (k : ℕ) (x : ℕ → α) : Fin k → α := fun i => x i

lemma psum_consN (a : ℝ) (f : ℕ → ℝ) (j : ℕ) : psum (consN a f) (j + 1) = a + psum f j := by
  unfold psum
  rw [Finset.sum_range_succ', add_comm]
  rfl

lemma Ev_zero_iff (t : ℝ) (x : ℕ → ℝ) : Ev t 0 x ↔ t < x 0 := by
  simp [Ev, psum]

lemma Ev_consN (t a : ℝ) (k : ℕ) (f : ℕ → ℝ) :
    Ev t (k + 1) (consN a f) ↔ a ≤ t ∧ Ev (t - a) k f := by
  unfold Ev
  simp only [psum_consN]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by have := h1 0 (Nat.succ_pos k); simpa [psum] using this, fun j hj => ?_, by linarith⟩
    have := h1 (j + 1) (by omega)
    linarith
  · rintro ⟨ha, h1, h2⟩
    refine ⟨fun j hj => ?_, by linarith⟩
    cases j with
    | zero => simpa [psum] using ha
    | succ j => have := h1 j (by omega); linarith

lemma postK_consN (t a : ℝ) (k : ℕ) (f : ℕ → ℝ) :
    postK t (k + 1) (consN a f) = postK (t - a) k f := by
  funext j
  unfold postK
  by_cases hj : j = 0
  · simp only [hj, if_true, psum_consN]; ring
  · simp only [hj, if_false]
    rw [show k + 1 + j = (k + j) + 1 by omega]
    rfl

lemma postK_zero_consN (t a : ℝ) (f : ℕ → ℝ) : postK t 0 (consN a f) = consN (a - t) f := by
  funext j
  unfold postK
  cases j with
  | zero => simp [psum]
  | succ j => simp

lemma preK_consN {α : Type*} (a : α) (k : ℕ) (f : ℕ → α) :
    preK (k + 1) (consN a f) = Fin.cons a (preK k f) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [preK]
  · simp [preK]

lemma measurable_psum (n : ℕ) : Measurable fun x : ℕ → ℝ => psum x n := by
  unfold psum
  exact Finset.measurable_sum _ fun m _ => measurable_pi_apply m

lemma measurableSet_Ev (t : ℝ) (k : ℕ) : MeasurableSet {x : ℕ → ℝ | Ev t k x} := by
  simp only [Ev, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_psum _) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_psum _))

lemma measurable_postK (t : ℝ) (k : ℕ) : Measurable (postK t k) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j = 0
  · simp only [postK, hj, if_true]; exact (measurable_psum _).sub_const _
  · simp only [postK, hj, if_false]; exact measurable_pi_apply _

lemma measurable_preK {α : Type*} [MeasurableSpace α] (k : ℕ) : Measurable (preK (α := α) k) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- the integrand of the restart identity. -/
noncomputable def L (ν : Measure ℝ) (t : ℝ) (k : ℕ) (g : (Fin k → ℝ) → ENNReal)
    (B : Set (ℕ → ℝ)) : ENNReal :=
  ∫⁻ x, {x | Ev t k x}.indicator (fun x => g (preK k x) * B.indicator 1 (postK t k x)) x
    ∂(Measure.infinitePi fun _ : ℕ => ν)

lemma measurable_integrand (t : ℝ) (k : ℕ) {g : (Fin k → ℝ) → ENNReal} (hg : Measurable g)
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    Measurable ({x | Ev t k x}.indicator
      (fun x => g (preK k x) * B.indicator (1 : (ℕ → ℝ) → ENNReal) (postK t k x))) :=
  ((hg.comp (measurable_preK k)).mul
    ((measurable_one.indicator hB).comp (measurable_postK t k))).indicator (measurableSet_Ev t k)

/-- Fubini step: condition on the first interarrival. -/
lemma L_succ {r : ℝ} (hr : 0 < r) (t : ℝ) (k : ℕ) {g : (Fin (k + 1) → ℝ) → ENNReal}
    (hg : Measurable g) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    L (expMeasure r) t (k + 1) g B =
      ∫⁻ a, (Iic t).indicator
        (fun a => L (expMeasure r) (t - a) k (fun y => g (Fin.cons a y)) B) a ∂(expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have hF := measurable_integrand t (k + 1) hg hB
  unfold L
  conv_lhs => rw [← map_consN (expMeasure r)]
  rw [lintegral_map hF measurable_consN]
  refine (lintegral_prod _ (hF.comp measurable_consN).aemeasurable).trans ?_
  refine lintegral_congr fun a => ?_
  by_cases ha : a ≤ t
  · rw [indicator_of_mem (show a ∈ Iic t from ha)]
    refine lintegral_congr fun f => ?_
    change {x | Ev t (k + 1) x}.indicator (fun x => g (preK (k + 1) x) *
        B.indicator 1 (postK t (k + 1) x)) (consN a f) =
      {x | Ev (t - a) k x}.indicator (fun x => g (Fin.cons a (preK k x)) *
        B.indicator 1 (postK (t - a) k x)) f
    by_cases hf : Ev (t - a) k f
    · rw [indicator_of_mem (show consN a f ∈ {x | Ev t (k + 1) x} from (Ev_consN t a k f).2 ⟨ha, hf⟩),
        indicator_of_mem (show f ∈ {x | Ev (t - a) k x} from hf), preK_consN, postK_consN]
    · rw [indicator_of_notMem (show consN a f ∉ {x | Ev t (k + 1) x} from
          fun h => hf ((Ev_consN t a k f).1 h).2),
        indicator_of_notMem (show f ∉ {x | Ev (t - a) k x} from hf)]
  · rw [indicator_of_notMem (show a ∉ Iic t from ha)]
    refine (lintegral_eq_zero_iff ((hF.comp measurable_consN).comp measurable_prodMk_left)).2
      (Filter.Eventually.of_forall fun f => ?_)
    simp only [Function.comp, Set.indicator, Set.mem_ofPred_eq, Ev_consN, ha, false_and,
      if_false, Pi.zero_apply]

lemma L_zero {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) (g : (Fin 0 → ℝ) → ENNReal)
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    L (expMeasure r) t 0 g B = ENNReal.ofReal (Real.exp (-(r * t))) * g Fin.elim0 *
      (Measure.infinitePi fun _ : ℕ => expMeasure r) B := by
  haveI := isProbabilityMeasure_expMeasure hr
  set P := Measure.infinitePi fun _ : ℕ => expMeasure r
  have hg : Measurable g := measurable_of_finite g
  have hF := measurable_integrand t 0 hg hB
  have hc : Measurable fun p : ℝ × (ℕ → ℝ) => B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN p.1 p.2) :=
    (measurable_one.indicator hB).comp measurable_consN
  unfold L
  conv_lhs => rw [← map_consN (expMeasure r)]
  rw [lintegral_map hF measurable_consN]
  refine (lintegral_prod _ (hF.comp measurable_consN).aemeasurable).trans ?_
  have hin : ∀ a, ∫⁻ f, ({x | Ev t 0 x}.indicator (fun x => g (preK 0 x) *
      B.indicator 1 (postK t 0 x))) (consN a f) ∂P =
      (Ioi t).indicator (fun a => g Fin.elim0 *
        ∫⁻ f, B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN (a - t) f) ∂P) a := by
    intro a
    by_cases ha : t < a
    · rw [indicator_of_mem (show a ∈ Ioi t from ha), ← lintegral_const_mul]
      · refine lintegral_congr fun f => ?_
        change {x | Ev t 0 x}.indicator (fun x => g (preK 0 x) *
            B.indicator 1 (postK t 0 x)) (consN a f) = _
        rw [indicator_of_mem (show consN a f ∈ {x | Ev t 0 x} from (Ev_zero_iff t _).2 ha),
          postK_zero_consN, Subsingleton.elim (preK 0 (consN a f)) Fin.elim0]
      · exact hc.comp measurable_prodMk_left
    · rw [indicator_of_notMem (show a ∉ Ioi t from ha)]
      refine (lintegral_eq_zero_iff ((hF.comp measurable_consN).comp measurable_prodMk_left)).2
        (Filter.Eventually.of_forall fun f => ?_)
      simp only [Function.comp, Set.indicator, Set.mem_ofPred_eq, Ev_zero_iff, consN_zero, ha,
        if_false, Pi.zero_apply]
  refine (lintegral_congr fun a => hin a).trans ?_
  have hh : Measurable fun b => g Fin.elim0 *
      ∫⁻ f, B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN b f) ∂P :=
    measurable_const.mul (hc.lintegral_prod_right')
  have hPB : ∫⁻ b, ∫⁻ f, B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN b f) ∂P ∂(expMeasure r)
      = P B := by
    calc ∫⁻ b, ∫⁻ f, B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN b f) ∂P ∂(expMeasure r)
        = ∫⁻ z, B.indicator (1 : (ℕ → ℝ) → ENNReal) (consN z.1 z.2) ∂((expMeasure r).prod P) :=
          (lintegral_prod _ hc.aemeasurable).symm
      _ = ∫⁻ x, B.indicator (1 : (ℕ → ℝ) → ENNReal) x
            ∂(((expMeasure r).prod P).map fun p : ℝ × (ℕ → ℝ) => consN p.1 p.2) :=
          (lintegral_map (measurable_one.indicator hB) measurable_consN).symm
      _ = P B := by rw [map_consN, lintegral_indicator_one hB]
  rw [expMeasure_memoryless ht hh, lintegral_const_mul _ hc.lintegral_prod_right', hPB, mul_assoc]

lemma measurable_fin_cons_left {α : Type*} [MeasurableSpace α] {k : ℕ} (a : α) :
    Measurable fun y : Fin k → α => (Fin.cons a y : Fin (k + 1) → α) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply j

/-- the restart identity, factored form: `L t k g B = c · P(B)`. -/
theorem L_factor {r : ℝ} (hr : 0 < r) (k : ℕ) : ∀ (t : ℝ), 0 ≤ t →
    ∀ (g : (Fin k → ℝ) → ENNReal), Measurable g →
    ∃ c : ENNReal, ∀ B : Set (ℕ → ℝ), MeasurableSet B →
      L (expMeasure r) t k g B = c * (Measure.infinitePi fun _ : ℕ => expMeasure r) B := by
  haveI := isProbabilityMeasure_expMeasure hr
  induction k with
  | zero => intro t ht g _; exact ⟨_, fun B hB => L_zero hr ht g hB⟩
  | succ k ih =>
    intro t ht g hg
    have hc : ∀ a : ℝ, ∃ c : ENNReal, a ≤ t → ∀ B : Set (ℕ → ℝ), MeasurableSet B →
        L (expMeasure r) (t - a) k (fun y => g (Fin.cons a y)) B =
          c * (Measure.infinitePi fun _ : ℕ => expMeasure r) B := by
      intro a
      by_cases ha : a ≤ t
      · obtain ⟨c, hc⟩ := ih (t - a) (by linarith) (fun y => g (Fin.cons a y))
          (hg.comp (measurable_fin_cons_left a))
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h ha⟩
    choose c hc using hc
    refine ⟨∫⁻ a, (Iic t).indicator c a ∂(expMeasure r), fun B hB => ?_⟩
    rw [L_succ hr t k hg hB, ← lintegral_mul_const' _ _ (measure_ne_top _ B)]
    refine lintegral_congr fun a => ?_
    by_cases ha : a ≤ t
    · rw [indicator_of_mem (show a ∈ Iic t from ha), indicator_of_mem (show a ∈ Iic t from ha),
        hc a ha B hB]
    · rw [indicator_of_notMem (show a ∉ Iic t from ha), indicator_of_notMem (show a ∉ Iic t from ha),
        zero_mul]

lemma Ev_unique {t : ℝ} {k k' : ℕ} {x : ℕ → ℝ} (h : Ev t k x) (h' : Ev t k' x) : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd (h'.1 k hlt) (not_le.2 h.2)
  · exact heq
  · exact absurd (h.1 k' hgt) (not_le.2 h'.2)

open Classical in
/-- the number of arrivals in `[0, t]` (junk `0` off the full-measure event). -/
noncomputable def Nidx (t : ℝ) (x : ℕ → ℝ) : ℕ := if h : ∃ k, Ev t k x then Nat.find h else 0

lemma Nidx_eq {t : ℝ} {k : ℕ} {x : ℕ → ℝ} (h : Ev t k x) : Nidx t x = k := by
  classical
  unfold Nidx
  rw [dif_pos ⟨k, h⟩]
  exact Ev_unique (Nat.find_spec (⟨k, h⟩ : ∃ k, Ev t k x)) h

/-- the stream restarted at the deterministic time `t`. -/
noncomputable def post (t : ℝ) (x : ℕ → ℝ) : ℕ → ℝ := postK t (Nidx t x) x

lemma measurable_Nidx (t : ℝ) : Measurable (Nidx t) := by
  refine measurable_to_countable' fun k => ?_
  have hE : MeasurableSet {x : ℕ → ℝ | ∃ k, Ev t k x} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_Ev t k
  have : Nidx t ⁻¹' {k} = {x | Ev t k x} ∪ ({x | ∃ k, Ev t k x}ᶜ ∩ {_x | k = 0}) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_compl_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hx
      by_cases h : ∃ k, Ev t k x
      · obtain ⟨k', hk'⟩ := h
        left; rw [Nidx_eq hk'] at hx; rwa [← hx]
      · right; refine ⟨h, ?_⟩
        rw [← hx]; unfold Nidx; rw [dif_neg h]
    · rintro (hx | ⟨hx, rfl⟩)
      · exact Nidx_eq hx
      · unfold Nidx; rw [dif_neg hx]
  rw [this]
  exact (measurableSet_Ev t k).union (hE.compl.inter (MeasurableSet.const _))

lemma measurable_post (t : ℝ) : Measurable (post t) := by
  have h2 : Measurable fun p : ℕ × (ℕ → ℝ) => postK t p.1 p.2 :=
    measurable_from_prod_countable_right fun k => measurable_postK t k
  exact h2.comp ((measurable_Nidx t).prodMk measurable_id)

/-- a.s. the stream has finitely many arrivals in `[0, t]` (strong law). -/
theorem ae_exists_Ev {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    haveI := isProbabilityMeasure_expMeasure hr
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => expMeasure r), ∃ k, Ev t k x := by
  haveI := isProbabilityMeasure_expMeasure hr
  set μ0 := Measure.infinitePi fun _ : ℕ => expMeasure r
  have hind : iIndepFun (fun (n : ℕ) (x : ℕ → ℝ) => x n) μ0 :=
    iIndepFun_infinitePi (X := fun _ y => y) (fun _ => measurable_id)
  have hid : ∀ n, IdentDistrib (fun x : ℕ → ℝ => x n) (fun x => x 0) μ0 μ0 :=
    fun n => ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable, by
      rw [(measurePreserving_eval_infinitePi _ n).map_eq,
        (measurePreserving_eval_infinitePi _ 0).map_eq]⟩
  have hmap := (measurePreserving_eval_infinitePi (fun _ : ℕ => expMeasure r) 0).map_eq
  have hint : Integrable (fun x : ℕ → ℝ => x 0) μ0 := by
    have h := (CMS.expMeasure_mean hr).1
    rw [← hmap] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_pi_apply _).aemeasurable).1 h
  have hmean : ∫ x, x 0 ∂μ0 = 1 / r := by
    have h := integral_map (μ := μ0) (φ := Function.eval 0) (f := fun y : ℝ => y)
      (measurable_pi_apply 0).aemeasurable measurable_id.aestronglyMeasurable
    rw [← (CMS.expMeasure_mean hr).2, ← hmap]
    exact h.symm
  have h := strong_law_ae_real (fun n (x : ℕ → ℝ) => x n) hint
    (fun i j hij => hind.indepFun hij) hid
  rw [hmean] at h
  filter_upwards [h] with x hx
  have hlt : 1 / (2 * r) < 1 / r := by
    rw [div_lt_div_iff₀ (by positivity) hr]; linarith
  obtain ⟨n, hn1, hn2⟩ := ((hx.eventually (lt_mem_nhds hlt)).and
    (Filter.eventually_gt_atTop ⌈2 * r * |t|⌉₊)).exists
  have h2 : 2 * r * |t| < n := Nat.lt_of_ceil_lt hn2
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) h2
  have h1 : 1 / (2 * r) * n < psum x n := by
    have := (lt_div_iff₀ hnpos).1 hn1
    simpa [psum] using this
  have h3 : |t| < 1 / (2 * r) * n := by
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)]; linarith
  have hex : ∃ m, t < psum x (m + 1) := by
    have htn : t < psum x n := lt_of_le_of_lt (le_abs_self t) (h3.trans h1)
    cases n with
    | zero => exact absurd htn (by simp [psum]; linarith)
    | succ m => exact ⟨m, htn⟩
  classical
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex⟩
  exact not_lt.1 (Nat.find_min hex hj)

lemma tsum_L {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    haveI := isProbabilityMeasure_expMeasure hr
    ∑' k, L (expMeasure r) t k (fun _ => 1) B =
      ∫⁻ x, B.indicator (1 : (ℕ → ℝ) → ENNReal) (post t x)
        ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  unfold L
  rw [← lintegral_tsum fun k => (measurable_integrand t k measurable_const hB).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_exists_Ev hr ht] with x hx
  obtain ⟨k0, hk0⟩ := hx
  rw [tsum_eq_single k0]
  · rw [indicator_of_mem (show x ∈ {x | Ev t k0 x} from hk0), one_mul, post, Nidx_eq hk0]
  · intro k hk
    exact indicator_of_notMem (show x ∉ {x | Ev t k x} from fun h => hk (Ev_unique h hk0)) _

/-- **Poisson restart (marginal).** The stream restarted at a deterministic time `t ≥ 0` is again an
i.i.d. `Exp r` stream. -/
theorem map_post {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    haveI := isProbabilityMeasure_expMeasure hr
    (Measure.infinitePi fun _ : ℕ => expMeasure r).map (post t) =
      Measure.infinitePi fun _ : ℕ => expMeasure r := by
  haveI := isProbabilityMeasure_expMeasure hr
  set P := Measure.infinitePi fun _ : ℕ => expMeasure r
  have hf := fun k => L_factor hr k t ht (fun _ => (1 : ENNReal)) measurable_const
  choose c hc using hf
  have e1 : ∀ B, MeasurableSet B → P (post t ⁻¹' B) = (∑' k, c k) * P B := by
    intro B hB
    rw [← ENNReal.tsum_mul_right]
    have : ∀ k, c k * P B = L (expMeasure r) t k (fun _ => 1) B := fun k => (hc k B hB).symm
    simp_rw [this]
    rw [tsum_L hr ht hB, ← lintegral_indicator_one (measurable_post t hB)]
    rfl
  have hsum : ∑' k, c k = 1 := by
    have := e1 univ MeasurableSet.univ
    rw [preimage_univ, measure_univ, mul_one] at this
    exact this.symm
  ext B hB
  rw [Measure.map_apply (measurable_post t) hB, e1 B hB, hsum, one_mul]

/-- **Poisson restart (independence).** Given exactly `k` arrivals in `[0, t]`, the restarted
stream is independent of the first `k` interarrival times. -/
theorem restart_indep {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {g : (Fin k → ℝ) → ENNReal} (hg : Measurable g) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    haveI := isProbabilityMeasure_expMeasure hr
    ∫⁻ x, {x | Ev t k x}.indicator (fun x => g (preK k x) *
        B.indicator (1 : (ℕ → ℝ) → ENNReal) (post t x)) x
        ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) =
      (∫⁻ x, {x | Ev t k x}.indicator (fun x => g (preK k x)) x
        ∂(Measure.infinitePi fun _ : ℕ => expMeasure r)) *
        (Measure.infinitePi fun _ : ℕ => expMeasure r) B := by
  haveI := isProbabilityMeasure_expMeasure hr
  obtain ⟨c, hc⟩ := L_factor hr k t ht g hg
  have h1 : ∫⁻ x, {x | Ev t k x}.indicator (fun x => g (preK k x) *
        B.indicator (1 : (ℕ → ℝ) → ENNReal) (post t x)) x
        ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) = L (expMeasure r) t k g B := by
    unfold L
    refine lintegral_congr fun x => ?_
    by_cases hx : Ev t k x
    · rw [indicator_of_mem (show x ∈ {x | Ev t k x} from hx),
        indicator_of_mem (show x ∈ {x | Ev t k x} from hx), post, Nidx_eq hx]
    · rw [indicator_of_notMem (show x ∉ {x | Ev t k x} from hx),
        indicator_of_notMem (show x ∉ {x | Ev t k x} from hx)]
  have h2 : ∫⁻ x, {x | Ev t k x}.indicator (fun x => g (preK k x)) x
      ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) = L (expMeasure r) t k g univ := by
    unfold L
    refine lintegral_congr fun x => ?_
    simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [h1, h2, hc B hB, hc univ MeasurableSet.univ, measure_univ, mul_one]

/-! ### marks: shifting an i.i.d. stream -/

/-- drop the first `n` entries. -/
def shiftN {α : Type*} (n : ℕ) (e : ℕ → α) : ℕ → α := fun m => e (n + m)

lemma shiftN_consN {α : Type*} (a : α) (f : ℕ → α) (n : ℕ) :
    shiftN (n + 1) (consN a f) = shiftN n f := by
  funext m
  simp only [shiftN]
  rw [show n + 1 + m = (n + m) + 1 by omega]
  rfl

lemma measurable_shiftN {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (shiftN (α := α) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

lemma lintegral_consN {α : Type*} [MeasurableSpace α] (η : Measure α) [IsProbabilityMeasure η]
    {F : (ℕ → α) → ENNReal} (hF : Measurable F) :
    ∫⁻ e, F e ∂(Measure.infinitePi fun _ : ℕ => η) =
      ∫⁻ a, ∫⁻ f, F (consN a f) ∂(Measure.infinitePi fun _ : ℕ => η) ∂η := by
  conv_lhs => rw [← map_consN η]
  rw [lintegral_map hF measurable_consN]
  exact lintegral_prod _ (hF.comp measurable_consN).aemeasurable

/-- the first `n` entries and the shifted stream are independent; the shift preserves the law. -/
theorem shift_indep {α : Type*} [MeasurableSpace α] (η : Measure α) [IsProbabilityMeasure η]
    (n : ℕ) : ∀ (g : (Fin n → α) → ENNReal), Measurable g →
    ∀ (C : Set (ℕ → α)), MeasurableSet C →
    ∫⁻ e, g (preK n e) * C.indicator 1 (shiftN n e) ∂(Measure.infinitePi fun _ : ℕ => η) =
      (∫⁻ e, g (preK n e) ∂(Measure.infinitePi fun _ : ℕ => η)) *
        (Measure.infinitePi fun _ : ℕ => η) C := by
  induction n with
  | zero =>
    intro g hg C hC
    have h0 : ∀ e : ℕ → α, preK 0 e = Fin.elim0 := fun e => Subsingleton.elim _ _
    have hs : ∀ e : ℕ → α, shiftN 0 e = e := fun e => funext fun m => by simp [shiftN]
    simp only [h0, hs]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      lintegral_const, measure_univ, mul_one]
  | succ n ih =>
    intro g hg C hC
    have hF : Measurable fun e => g (preK (n + 1) e) *
        C.indicator (1 : (ℕ → α) → ENNReal) (shiftN (n + 1) e) :=
      (hg.comp (measurable_preK _)).mul ((measurable_one.indicator hC).comp (measurable_shiftN _))
    have hG : Measurable fun e => g (preK (n + 1) e) := hg.comp (measurable_preK _)
    rw [lintegral_consN η hF, lintegral_consN η hG]
    simp only [preK_consN, shiftN_consN]
    refine (lintegral_congr fun a => ih (fun y => g (Fin.cons a y))
      (hg.comp (measurable_fin_cons_left a)) C hC).trans ?_
    exact lintegral_mul_const' _ _ (measure_ne_top _ _)

theorem shift_indep_set {α : Type*} [MeasurableSpace α] (η : Measure α) [IsProbabilityMeasure η]
    (n : ℕ) {A : Set (Fin n → α)} (hA : MeasurableSet A) {C : Set (ℕ → α)} (hC : MeasurableSet C) :
    (Measure.infinitePi fun _ : ℕ => η) (preK n ⁻¹' A ∩ shiftN n ⁻¹' C) =
      (Measure.infinitePi fun _ : ℕ => η) (preK n ⁻¹' A) *
        (Measure.infinitePi fun _ : ℕ => η) C := by
  have h := shift_indep η n (A.indicator 1) (measurable_one.indicator hA) C hC
  have e1 : ∀ e : ℕ → α, A.indicator (1 : (Fin n → α) → ENNReal) (preK n e) *
      C.indicator 1 (shiftN n e) = (preK n ⁻¹' A ∩ shiftN n ⁻¹' C).indicator 1 e := by
    intro e
    by_cases ha : preK n e ∈ A <;> by_cases hc : shiftN n e ∈ C <;>
      simp [Set.indicator_apply, ha, hc]
  have e2 : ∀ e : ℕ → α, A.indicator (1 : (Fin n → α) → ENNReal) (preK n e) =
      (preK n ⁻¹' A).indicator 1 e := by
    intro e
    by_cases ha : preK n e ∈ A <;> simp [Set.indicator_apply, ha]
  simp only [e1] at h
  simp only [e2] at h
  rwa [lintegral_indicator_one (((measurable_preK n) hA).inter ((measurable_shiftN n) hC)),
    lintegral_indicator_one ((measurable_preK n) hA)] at h

/-- integrate over the number of arrivals in `[0, t]`. -/
lemma lintegral_eq_tsum_Ev {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t)
    {F : ℕ → (ℕ → ℝ) → ENNReal} (hF : ∀ n, Measurable (F n)) :
    haveI := isProbabilityMeasure_expMeasure hr
    ∫⁻ x, F (Nidx t x) x ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) =
      ∑' n, ∫⁻ x, {x | Ev t n x}.indicator (F n) x
        ∂(Measure.infinitePi fun _ : ℕ => expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [← lintegral_tsum fun n => ((hF n).indicator (measurableSet_Ev t n)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_exists_Ev hr ht] with x hx
  obtain ⟨k0, hk0⟩ := hx
  rw [tsum_eq_single k0, indicator_of_mem (show x ∈ {x | Ev t k0 x} from hk0), Nidx_eq hk0]
  intro k hk
  exact indicator_of_notMem (show x ∉ {x | Ev t k x} from fun h => hk (Ev_unique h hk0)) _

/-! ### one marked stream restarted at a deterministic time: independence, measure level -/

section Marked
variable {E : Type*} [MeasurableSpace E]

/-- the work brought by the arrivals in `[0, t]` (marks `z.2.1` are the service requirements). -/
noncomputable def cW (t : ℝ) (z : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) : ℝ :=
  ∑ m ∈ Finset.range (Nidx t z.1), z.2.1 m

/-- the marked stream restarted at `t`. -/
noncomputable def thc (t : ℝ) (z : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) :
    (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E) :=
  (post t z.1, shiftN (Nidx t z.1) z.2.1, shiftN (Nidx t z.1) z.2.2)

lemma measurable_cW (t : ℝ) : Measurable (cW (E := E) t) := by
  have h : Measurable fun p : ℕ × ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) =>
      ∑ m ∈ Finset.range p.1, p.2.2.1 m :=
    measurable_from_prod_countable_right fun n =>
      (show Measurable fun y : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E) => ∑ m ∈ Finset.range n, y.2.1 m from
        Finset.measurable_sum _ fun m _ => (measurable_pi_apply m).comp measurable_snd.fst)
  exact h.comp (((measurable_Nidx t).comp measurable_fst).prodMk measurable_id)

lemma measurable_thc (t : ℝ) : Measurable (thc (E := E) t) := by
  have h1 : Measurable fun p : ℕ × ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) => shiftN p.1 p.2.2.1 :=
    measurable_from_prod_countable_right fun n => (measurable_shiftN n).comp measurable_snd.fst
  have h2 : Measurable fun p : ℕ × ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) => shiftN p.1 p.2.2.2 :=
    measurable_from_prod_countable_right fun n => (measurable_shiftN n).comp measurable_snd.snd
  have hN : Measurable fun z : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E) => (Nidx t z.1, z) :=
    ((measurable_Nidx t).comp measurable_fst).prodMk measurable_id
  exact ((measurable_post t).comp measurable_fst).prodMk ((h1.comp hN).prodMk (h2.comp hN))

variable {r : ℝ} (η1 : Measure ℝ) [IsProbabilityMeasure η1]
  (η2 : Measure E) [IsProbabilityMeasure η2]

/-- the rectangle formula behind the independence of `cW` and `thc`. -/
theorem rect_formula (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) {s : Set ℝ} (hs : MeasurableSet s)
    {C0 C1 : Set (ℕ → ℝ)} {C2 : Set (ℕ → E)} (h0 : MeasurableSet C0) (h1 : MeasurableSet C1)
    (h2 : MeasurableSet C2) :
    haveI := isProbabilityMeasure_expMeasure hr
    ((Measure.infinitePi fun _ : ℕ => expMeasure r).prod
      ((Measure.infinitePi fun _ : ℕ => η1).prod (Measure.infinitePi fun _ : ℕ => η2)))
      (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2)) =
    (∑' n, (Measure.infinitePi fun _ : ℕ => expMeasure r) {x | Ev t n x} *
        (Measure.infinitePi fun _ : ℕ => η1) (preK n ⁻¹' {y : Fin n → ℝ | ∑ i, y i ∈ s})) *
      ((Measure.infinitePi fun _ : ℕ => expMeasure r) C0 *
        ((Measure.infinitePi fun _ : ℕ => η1) C1 * (Measure.infinitePi fun _ : ℕ => η2) C2)) := by
  haveI := isProbabilityMeasure_expMeasure hr
  set P0 := Measure.infinitePi fun _ : ℕ => expMeasure r
  set P1 := Measure.infinitePi fun _ : ℕ => η1
  set P2 := Measure.infinitePi fun _ : ℕ => η2
  have hAs : ∀ n, MeasurableSet {y : Fin n → ℝ | ∑ i, y i ∈ s} := fun n =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) hs
  have hS : MeasurableSet (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2)) :=
    ((measurable_cW t) hs).inter ((measurable_thc t) (h0.prod (h1.prod h2)))
  set k : ℕ → ENNReal := fun n => P1 (preK n ⁻¹' {y : Fin n → ℝ | ∑ i, y i ∈ s}) * (P1 C1 * P2 C2)
  have hslice : ∀ x : ℕ → ℝ, (P1.prod P2) (Prod.mk x ⁻¹' (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2)))
      = k (Nidx t x) * C0.indicator 1 (post t x) := by
    intro x
    set n := Nidx t x
    by_cases hp : post t x ∈ C0
    · have : Prod.mk x ⁻¹' (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2)) =
          (preK n ⁻¹' {y : Fin n → ℝ | ∑ i, y i ∈ s} ∩ shiftN n ⁻¹' C1) ×ˢ (shiftN n ⁻¹' C2) := by
        ext ⟨e1, e2⟩
        simp only [mem_preimage, mem_inter_iff, mem_prod, cW, thc, preK, Set.mem_ofPred_eq, hp,
          true_and, Fin.sum_univ_eq_sum_range (fun m => e1 m) n]
        tauto
      rw [this, Measure.prod_prod, shift_indep_set η1 n (hAs n) h1, indicator_of_mem hp,
        Pi.one_apply, mul_one]
      have h2' := shift_indep_set η2 n (A := univ) MeasurableSet.univ h2
      rw [preimage_univ, univ_inter, measure_univ, one_mul] at h2'
      rw [h2', mul_assoc]
    · have : Prod.mk x ⁻¹' (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2)) = ∅ := by
        ext ⟨e1, e2⟩
        simp only [mem_preimage, mem_inter_iff, mem_prod, thc, hp, false_and, and_false,
          mem_empty_iff_false]
      rw [this, measure_empty, indicator_of_notMem hp, mul_zero]
  rw [Measure.prod_apply hS]
  simp_rw [hslice]
  rw [lintegral_eq_tsum_Ev hr ht (F := fun n x => k n * C0.indicator 1 (post t x))
    (fun n => measurable_const.mul ((measurable_one.indicator h0).comp (measurable_post t)))]
  have hterm : ∀ n, ∫⁻ x, {x | Ev t n x}.indicator (fun x => k n * C0.indicator 1 (post t x)) x ∂P0
      = (P0 {x | Ev t n x} * P1 (preK n ⁻¹' {y : Fin n → ℝ | ∑ i, y i ∈ s})) *
        (P0 C0 * (P1 C1 * P2 C2)) := by
    intro n
    have h := restart_indep hr ht n (g := fun _ => k n) measurable_const h0
    rw [h, lintegral_indicator_const (measurableSet_Ev t n)]
    simp only [k]
    ring
  refine (tsum_congr fun n => hterm n).trans ?_
  exact ENNReal.tsum_mul_right

/-- **Restart of a marked stream.** The work brought before `t` is independent of the restarted
marked stream, which has the original law. -/
theorem map_cW_thc (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    haveI := isProbabilityMeasure_expMeasure hr
    ((Measure.infinitePi fun _ : ℕ => expMeasure r).prod
      ((Measure.infinitePi fun _ : ℕ => η1).prod (Measure.infinitePi fun _ : ℕ => η2))).map
        (fun z => (cW t z, thc t z)) =
    ((((Measure.infinitePi fun _ : ℕ => expMeasure r).prod
      ((Measure.infinitePi fun _ : ℕ => η1).prod (Measure.infinitePi fun _ : ℕ => η2))).map
        (cW t)).prod
      ((Measure.infinitePi fun _ : ℕ => expMeasure r).prod
        ((Measure.infinitePi fun _ : ℕ => η1).prod (Measure.infinitePi fun _ : ℕ => η2)))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  set P0 := Measure.infinitePi fun _ : ℕ => expMeasure r
  set P1 := Measure.infinitePi fun _ : ℕ => η1
  set P2 := Measure.infinitePi fun _ : ℕ => η2
  set Q := P0.prod (P1.prod P2)
  have hcW := measurable_cW (E := E) t
  have hth := measurable_thc (E := E) t
  have hK : ∀ s, MeasurableSet s → Q (cW t ⁻¹' s) =
      ∑' n, P0 {x | Ev t n x} * P1 (preK n ⁻¹' {y : Fin n → ℝ | ∑ i, y i ∈ s}) := by
    intro s hs
    have h := rect_formula η1 η2 hr ht hs (C0 := univ) (C1 := univ) (C2 := univ)
      MeasurableSet.univ MeasurableSet.univ MeasurableSet.univ
    simp only [univ_prod_univ, preimage_univ, inter_univ, measure_univ, mul_one] at h
    exact h
  refine (Measure.prod_eq fun s C hs hC => ?_).symm
  rw [Measure.map_apply (hcW.prodMk hth) (hs.prod hC), mk_preimage_prod,
    Measure.map_apply hcW hs]
  -- level 1: the measure `C ↦ Q (cW⁻¹ s ∩ thc⁻¹ C)` is `Q (cW⁻¹ s) • Q`
  set c : NNReal := (Q (cW t ⁻¹' s)).toNNReal
  have hc : (c : ENNReal) = Q (cW t ⁻¹' s) := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hm2 : Measurable fun z : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E) => (thc t z).2 := hth.snd
  have lvl1 : (Q.restrict (cW t ⁻¹' s)).map (thc t) = (c • P0).prod (P1.prod P2) := by
    refine (Measure.prod_eq fun C0 C' h0 hC' => ?_).symm
    rw [Measure.map_apply hth (h0.prod hC'), Measure.restrict_apply (hth (h0.prod hC'))]
    set c2 : NNReal := (Q (cW t ⁻¹' s) * P0 C0).toNNReal
    have hc2 : (c2 : ENNReal) = Q (cW t ⁻¹' s) * P0 C0 :=
      ENNReal.coe_toNNReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    -- level 2
    have lvl2 : (Q.restrict (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ univ))).map (fun z => (thc t z).2) =
        (c2 • P1).prod P2 := by
      refine (Measure.prod_eq fun C1 C2 h1 h2 => ?_).symm
      rw [Measure.map_apply hm2 (h1.prod h2), Measure.restrict_apply (hm2 (h1.prod h2))]
      have hset : (fun z => (thc t z).2) ⁻¹' (C1 ×ˢ C2) ∩ (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ univ)) =
          cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ C1 ×ˢ C2) := by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
        tauto
      rw [hset, rect_formula η1 η2 hr ht hs h0 h1 h2, ← hK s hs, Measure.smul_apply,
        ENNReal.smul_def, smul_eq_mul, hc2]
      ring
    have hset1 : thc t ⁻¹' (C0 ×ˢ C') ∩ cW t ⁻¹' s =
        (fun z => (thc t z).2) ⁻¹' C' ∩ (cW t ⁻¹' s ∩ thc t ⁻¹' (C0 ×ˢ univ)) := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
      tauto
    have e2 := congrArg (fun μ : Measure ((ℕ → ℝ) × (ℕ → E)) => μ C') lvl2
    rw [Measure.map_apply hm2 hC', Measure.restrict_apply (hm2 hC')] at e2
    rw [hset1, e2, Measure.prod_smul_left, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, hc2, hc, mul_assoc]
  have e1 := congrArg (fun μ : Measure ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)) => μ C) lvl1
  rw [Measure.map_apply hth hC, Measure.restrict_apply (hth hC), Measure.prod_smul_left,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc] at e1
  rw [inter_comm, e1]

end Marked

end CMR


/-! ## P2b: the multi-class sample space as a product of independent marked streams, and the
split of one class's first job.  Mathlib only (uses CMR from P2a). -/

namespace CMT
open MeasureTheory ProbabilityTheory Set Function CMR

section Streams
variable {M : ℕ} {E : Type*} [MeasurableSpace E]

/-- one marked stream: interarrival times, service requirements, marks. -/
abbrev Str (E : Type*) := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → E)

/-- the multi-class sample space (the platform's `Omega M` with `E = ℕ → unitInterval`). -/
abbrev Om (M : ℕ) (E : Type*) := (Fin M × ℕ → ℝ) × (Fin M × ℕ → ℝ) × (Fin M × ℕ → E)

/-- per-class streams of a sample point. -/
def toS (ω : Om M E) : Fin M → Str E :=
  fun k => (fun m => ω.1 (k, m), fun m => ω.2.1 (k, m), fun m => ω.2.2 (k, m))

/-- the sample point of a family of per-class streams. -/
def ofS (z : Fin M → Str E) : Om M E :=
  (fun j => (z j.1).1 j.2, fun j => (z j.1).2.1 j.2, fun j => (z j.1).2.2 j.2)

@[simp] lemma ofS_toS (ω : Om M E) : ofS (toS ω) = ω := rfl
@[simp] lemma toS_ofS (z : Fin M → Str E) : toS (ofS z) = z := rfl

lemma measurable_toS : Measurable (toS (M := M) (E := E)) := by
  refine measurable_pi_lambda _ fun k => ?_
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun m => (measurable_pi_apply (k, m)).comp measurable_fst
  · exact measurable_pi_lambda _ fun m => (measurable_pi_apply (k, m)).comp measurable_snd.fst
  · exact measurable_pi_lambda _ fun m => (measurable_pi_apply (k, m)).comp measurable_snd.snd

lemma measurable_ofS : Measurable (ofS (M := M) (E := E)) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply j.2).comp (measurable_fst.comp (measurable_pi_apply j.1))
  · exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply j.2).comp (measurable_snd.fst.comp (measurable_pi_apply j.1))
  · exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply j.2).comp (measurable_snd.snd.comp (measurable_pi_apply j.1))

/-- the law of one marked stream. -/
noncomputable def Qs (a b : Measure ℝ) [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    (η : Measure E) [IsProbabilityMeasure η] : Measure (Str E) :=
  (Measure.infinitePi fun _ : ℕ => a).prod
    ((Measure.infinitePi fun _ : ℕ => b).prod (Measure.infinitePi fun _ : ℕ => η))

instance (a b : Measure ℝ) [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    (η : Measure E) [IsProbabilityMeasure η] : IsProbabilityMeasure (Qs a b η) := by
  unfold Qs; infer_instance

variable (α β : Fin M → Measure ℝ) [∀ k, IsProbabilityMeasure (α k)]
  [∀ k, IsProbabilityMeasure (β k)] (η : Measure E) [IsProbabilityMeasure η]

/-- the multi-class law (the platform's `D.P` with `α k = Exp (λ k)`, `β k = Exp (μ k)`). -/
noncomputable def PO : Measure (Om M E) :=
  (Measure.infinitePi fun j : Fin M × ℕ => α j.1).prod
    ((Measure.infinitePi fun j : Fin M × ℕ => β j.1).prod
      (Measure.infinitePi fun _ : Fin M × ℕ => η))

instance : IsProbabilityMeasure (PO α β η) := by unfold PO; infer_instance

/-- **P2b-1.** The classes are independent marked streams. -/
theorem map_toS : (PO α β η).map toS = Measure.pi fun k => Qs (α k) (β k) η := by
  have ha := Measure.infinitePi_map_curry (fun (k : Fin M) (_ : ℕ) => α k)
  have hb := Measure.infinitePi_map_curry (fun (k : Fin M) (_ : ℕ) => β k)
  have hc := Measure.infinitePi_map_curry (fun (_ : Fin M) (_ : ℕ) => η)
  rw [Measure.infinitePi_eq_pi (ι := Fin M)] at ha hb hc
  beta_reduce at ha hb hc
  have h1 : (PO α β η).map (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ)
      (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ) (MeasurableEquiv.curry (Fin M) ℕ E))) =
      (Measure.pi fun k => Measure.infinitePi fun _ : ℕ => α k).prod
        ((Measure.pi fun k => Measure.infinitePi fun _ : ℕ => β k).prod
          (Measure.pi fun _ : Fin M => Measure.infinitePi fun _ : ℕ => η)) := by
    rw [← ha, ← hb, ← hc, Measure.map_prod_map _ _ (MeasurableEquiv.measurable _)
      (MeasurableEquiv.measurable _), Measure.map_prod_map _ _ (MeasurableEquiv.measurable _)
      ((MeasurableEquiv.measurable _).prodMap (MeasurableEquiv.measurable _))]
    rfl
  have hA := measurePreserving_arrowProdEquivProdArrow (ℕ → ℝ) ((ℕ → ℝ) × (ℕ → E)) (Fin M)
    (fun k => Measure.infinitePi fun _ : ℕ => α k)
    (fun k => (Measure.infinitePi fun _ : ℕ => β k).prod (Measure.infinitePi fun _ : ℕ => η))
  have hB := measurePreserving_arrowProdEquivProdArrow (ℕ → ℝ) (ℕ → E) (Fin M)
    (fun k => Measure.infinitePi fun _ : ℕ => β k) (fun _ => Measure.infinitePi fun _ : ℕ => η)
  have hG := ((MeasurePreserving.id (Measure.pi fun k => Measure.infinitePi fun _ : ℕ => α k)).prod
    hB).comp hA
  have hGinv : Measurable fun p : (Fin M → ℕ → ℝ) × (Fin M → ℕ → ℝ) × (Fin M → ℕ → E) =>
      (fun k => (p.1 k, p.2.1 k, p.2.2 k) : Fin M → Str E) := by
    refine measurable_pi_lambda _ fun k => ?_
    exact ((measurable_pi_apply k).comp measurable_fst).prodMk
      (((measurable_pi_apply k).comp measurable_snd.fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd.snd))
  have hF : Measurable (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ)
      (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ) (MeasurableEquiv.curry (Fin M) ℕ E))) :=
    (MeasurableEquiv.measurable _).prodMap
      ((MeasurableEquiv.measurable _).prodMap (MeasurableEquiv.measurable _))
  calc (PO α β η).map toS
      = ((PO α β η).map (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ)
          (Prod.map (MeasurableEquiv.curry (Fin M) ℕ ℝ) (MeasurableEquiv.curry (Fin M) ℕ E)))).map
          (fun p : (Fin M → ℕ → ℝ) × (Fin M → ℕ → ℝ) × (Fin M → ℕ → E) =>
            (fun k => (p.1 k, p.2.1 k, p.2.2 k) : Fin M → Str E)) := by
        rw [Measure.map_map hGinv hF]; rfl
    _ = ((Measure.pi fun k => Qs (α k) (β k) η).map _).map
          (fun p : (Fin M → ℕ → ℝ) × (Fin M → ℕ → ℝ) × (Fin M → ℕ → E) => (fun k => (p.1 k, p.2.1 k, p.2.2 k) : Fin M → Str E)) := by
        rw [h1, ← hG.map_eq]; rfl
    _ = Measure.pi fun k => Qs (α k) (β k) η := by
        rw [Measure.map_map hGinv hG.measurable]
        exact Measure.map_id

/-! ### splitting off the first job of one class -/

section Rearr
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace D] (μ1 : Measure A) (μ2 : Measure B) (μ3 : Measure C) (μ4 : Measure D)
  [SFinite μ1] [SFinite μ2] [SFinite μ3] [SFinite μ4]

/-- the middle-swap of a fourfold product preserves the product measure. -/
theorem mp_ppcomm : MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    ((μ1.prod μ2).prod (μ3.prod μ4)) ((μ1.prod μ3).prod (μ2.prod μ4)) := by
  have e1 := measurePreserving_prodAssoc μ1 μ2 (μ3.prod μ4)
  have e2 := (MeasurePreserving.id μ1).prod (measurePreserving_prodAssoc μ2 μ3 μ4).symm
  have e3 := (MeasurePreserving.id μ1).prod
    ((Measure.measurePreserving_swap (μ := μ2) (ν := μ3)).prod (MeasurePreserving.id μ4))
  have e4 := (MeasurePreserving.id μ1).prod (measurePreserving_prodAssoc μ3 μ2 μ4)
  have e5 := (measurePreserving_prodAssoc μ1 μ3 (μ2.prod μ4)).symm
  exact (e5.comp (e4.comp (e3.comp (e2.comp e1))))

end Rearr

/-- prepend a job to a marked stream. -/
def consS (h : ℝ × ℝ × E) (s : Str E) : Str E :=
  (consN h.1 s.1, consN h.2.1 s.2.1, consN h.2.2 s.2.2)

/-- drop the first job of a marked stream. -/
def tailS (s : Str E) : Str E := (shiftN 1 s.1, shiftN 1 s.2.1, shiftN 1 s.2.2)

/-- the first job of a marked stream. -/
def headS (s : Str E) : ℝ × ℝ × E := (s.1 0, s.2.1 0, s.2.2 0)

@[simp] lemma tailS_consS (h : ℝ × ℝ × E) (s : Str E) : tailS (consS h s) = s := by
  simp only [tailS, consS, shiftN_consN]
  obtain ⟨a, b, c⟩ := s
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext m <;> exact congrArg _ (Nat.zero_add m)

@[simp] lemma headS_consS (h : ℝ × ℝ × E) (s : Str E) : headS (consS h s) = h := rfl

lemma measurable_consS : Measurable fun p : (ℝ × ℝ × E) × Str E => consS p.1 p.2 := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_consN.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  · exact measurable_consN.comp (measurable_fst.snd.fst.prodMk measurable_snd.snd.fst)
  · exact measurable_consN.comp (measurable_fst.snd.snd.prodMk measurable_snd.snd.snd)

/-- the law of one job (interarrival, requirement, mark). -/
noncomputable def Hs (a b : Measure ℝ) (η : Measure E) : Measure (ℝ × ℝ × E) := a.prod (b.prod η)

instance (a b : Measure ℝ) [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    (η : Measure E) [IsProbabilityMeasure η] : IsProbabilityMeasure (Hs a b η) := by
  unfold Hs; infer_instance

theorem map_consS (a b : Measure ℝ) [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    (η : Measure E) [IsProbabilityMeasure η] :
    ((Hs a b η).prod (Qs a b η)).map (fun p => consS p.1 p.2) = Qs a b η := by
  have r1 := mp_ppcomm a (b.prod η) (Measure.infinitePi fun _ : ℕ => a)
    ((Measure.infinitePi fun _ : ℕ => b).prod (Measure.infinitePi fun _ : ℕ => η))
  have r2 := (MeasurePreserving.id (a.prod (Measure.infinitePi fun _ : ℕ => a))).prod
    (mp_ppcomm b η (Measure.infinitePi fun _ : ℕ => b) (Measure.infinitePi fun _ : ℕ => η))
  have c1 : MeasurePreserving (fun p : ℝ × (ℕ → ℝ) => consN p.1 p.2)
      (a.prod (Measure.infinitePi fun _ : ℕ => a)) (Measure.infinitePi fun _ : ℕ => a) :=
    ⟨measurable_consN, map_consN a⟩
  have c2 : MeasurePreserving (fun p : ℝ × (ℕ → ℝ) => consN p.1 p.2)
      (b.prod (Measure.infinitePi fun _ : ℕ => b)) (Measure.infinitePi fun _ : ℕ => b) :=
    ⟨measurable_consN, map_consN b⟩
  have c3 : MeasurePreserving (fun p : E × (ℕ → E) => consN p.1 p.2)
      (η.prod (Measure.infinitePi fun _ : ℕ => η)) (Measure.infinitePi fun _ : ℕ => η) :=
    ⟨measurable_consN, map_consN η⟩
  exact ((c1.prod (c2.prod c3)).comp (r2.comp r1)).map_eq

variable {X : Type*} [MeasurableSpace X]

theorem map_update (Q : Fin M → Measure X) [∀ k, IsProbabilityMeasure (Q k)] (i : Fin M) :
    ((Q i).prod (Measure.pi Q)).map (fun p => update p.2 i p.1) = Measure.pi Q := by
  classical
  have hm : Measurable fun p : X × (Fin M → X) => update p.2 i p.1 :=
    measurable_update'.comp measurable_swap
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : X × (Fin M → X) => update p.2 i p.1) ⁻¹' Set.pi univ s =
      s i ×ˢ Set.pi univ (update s i univ) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun k => ?_⟩
      by_cases hk : k = i
      · subst hk; simp
      · simpa [update_of_ne hk] using h k
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simpa [update_of_ne hk] using h2 k
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∏ k, Q k (update s i univ k) = ∏ k ∈ Finset.univ.erase i, Q k (s k) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this, Finset.mul_prod_erase _ (fun k => Q k (s k)) (Finset.mem_univ i)]

/-- **split.** Under the product of the class laws, class `i`'s first job is independent of the
rest (class `i`'s tail and the other classes), which again have the product law. -/
theorem map_split (Q : Fin M → Measure (Str E)) [∀ k, IsProbabilityMeasure (Q k)] (i : Fin M)
    (H : Measure (ℝ × ℝ × E)) [IsProbabilityMeasure H]
    (hQ : (H.prod (Q i)).map (fun p => consS p.1 p.2) = Q i) :
    (H.prod (Measure.pi Q)).map (fun p => update p.2 i (consS p.1 (p.2 i))) = Measure.pi Q := by
  classical
  have hu : MeasurePreserving (fun p : Str E × (Fin M → Str E) => update p.2 i p.1)
      ((Q i).prod (Measure.pi Q)) (Measure.pi Q) :=
    ⟨measurable_update'.comp measurable_swap, map_update Q i⟩
  have g1 := (MeasurePreserving.id H).prod hu
  have hc : MeasurePreserving (fun p : (ℝ × ℝ × E) × Str E => consS p.1 p.2)
      (H.prod (Q i)) (Q i) := ⟨measurable_consS, hQ⟩
  have g2 := (hc.prod (MeasurePreserving.id (Measure.pi Q))).comp
    (measurePreserving_prodAssoc H (Q i) (Measure.pi Q)).symm
  have g3 := hu.comp g2
  have hΨ : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) => update p.2 i (consS p.1 (p.2 i)) :=
    measurable_update'.comp (measurable_snd.prodMk
      (measurable_consS.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))
  rw [← g1.map_eq, Measure.map_map hΨ g1.measurable]
  refine Eq.trans ?_ g3.map_eq
  congr 1
  funext p
  simp [MeasurableEquiv.prodAssoc, Equiv.prodAssoc]

/-! ### joint measurability in the restart time -/

lemma measurableSet_Ev₂ (k : ℕ) : MeasurableSet {p : ℝ × (ℕ → ℝ) | Ev p.1 k p.2} := by
  simp only [Ev, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le ((measurable_psum _).comp measurable_snd) measurable_fst).inter
    (measurableSet_lt measurable_fst ((measurable_psum _).comp measurable_snd))

lemma measurable_Nidx₂ : Measurable fun p : ℝ × (ℕ → ℝ) => Nidx p.1 p.2 := by
  refine measurable_to_countable' fun k => ?_
  have hE : MeasurableSet {p : ℝ × (ℕ → ℝ) | ∃ k, Ev p.1 k p.2} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_Ev₂ k
  have : (fun p : ℝ × (ℕ → ℝ) => Nidx p.1 p.2) ⁻¹' {k} =
      {p : ℝ × (ℕ → ℝ) | Ev p.1 k p.2} ∪
        ({p : ℝ × (ℕ → ℝ) | ∃ k, Ev p.1 k p.2}ᶜ ∩ {_p | k = 0}) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_compl_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hx
      by_cases h : ∃ k, Ev p.1 k p.2
      · obtain ⟨k', hk'⟩ := h
        left; rw [Nidx_eq hk'] at hx; rwa [← hx]
      · right; refine ⟨h, ?_⟩
        rw [← hx]; unfold Nidx; rw [dif_neg h]
    · rintro (hx | ⟨hx, rfl⟩)
      · exact Nidx_eq hx
      · unfold Nidx; rw [dif_neg hx]
  rw [this]
  exact (measurableSet_Ev₂ k).union (hE.compl.inter (MeasurableSet.const _))

lemma measurable_postK₂ (k : ℕ) : Measurable fun p : ℝ × (ℕ → ℝ) => postK p.1 k p.2 := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j = 0
  · simp only [postK, hj, if_true]
    exact ((measurable_psum _).comp measurable_snd).sub measurable_fst
  · simp only [postK, hj, if_false]; exact (measurable_pi_apply _).comp measurable_snd

lemma measurable_post₂ : Measurable fun p : ℝ × (ℕ → ℝ) => post p.1 p.2 := by
  have h2 : Measurable fun q : ℕ × (ℝ × (ℕ → ℝ)) => postK q.2.1 q.1 q.2.2 :=
    measurable_from_prod_countable_right fun k => measurable_postK₂ k
  exact h2.comp (measurable_Nidx₂.prodMk measurable_id)

lemma measurable_cW₂ : Measurable fun p : ℝ × Str E => cW p.1 p.2 := by
  have h : Measurable fun q : ℕ × (ℝ × Str E) => ∑ m ∈ Finset.range q.1, q.2.2.2.1 m :=
    measurable_from_prod_countable_right fun n =>
      (show Measurable fun y : ℝ × Str E => ∑ m ∈ Finset.range n, y.2.2.1 m from
        Finset.measurable_sum _ fun m _ => (measurable_pi_apply m).comp measurable_snd.snd.fst)
  exact h.comp ((measurable_Nidx₂.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    measurable_id)

lemma measurable_thc₂ : Measurable fun p : ℝ × Str E => thc p.1 p.2 := by
  have h1 : Measurable fun q : ℕ × (ℝ × Str E) => shiftN q.1 q.2.2.2.1 :=
    measurable_from_prod_countable_right fun n => (measurable_shiftN n).comp measurable_snd.snd.fst
  have h2 : Measurable fun q : ℕ × (ℝ × Str E) => shiftN q.1 q.2.2.2.2 :=
    measurable_from_prod_countable_right fun n => (measurable_shiftN n).comp measurable_snd.snd.snd
  have hN : Measurable fun p : ℝ × Str E => (Nidx p.1 p.2.1, p) :=
    (measurable_Nidx₂.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_id
  exact (measurable_post₂.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    ((h1.comp hN).prodMk (h2.comp hN))

/-! ### restarting all classes but `i` at a deterministic time -/

/-- per-class map at the restart time `T`: class `i` is kept, the others are restarted. -/
noncomputable def fk (i : Fin M) (T : ℝ) (k : Fin M) (s : Str E) : ℝ × Str E :=
  if k = i then (0, s) else (cW T s, thc T s)

lemma measurable_fk (i : Fin M) (T : ℝ) (k : Fin M) : Measurable (fk (E := E) i T k) := by
  by_cases hk : k = i
  · have : fk (E := E) i T k = fun s => (0, s) := by funext s; simp [fk, hk]
    rw [this]; exact measurable_const.prodMk measurable_id
  · have : fk (E := E) i T k = fun s => (cW T s, thc T s) := by funext s; simp [fk, hk]
    rw [this]; exact (measurable_cW T).prodMk (measurable_thc T)

/-- the other classes' work brought in `[0, T]`. -/
noncomputable def sumW (i : Fin M) (T : ℝ) (z : Fin M → Str E) : ℝ :=
  ∑ k, if k = i then 0 else cW T (z k)

/-- the other classes restarted at `T`, class `i` kept. -/
noncomputable def rest (i : Fin M) (T : ℝ) (z : Fin M → Str E) : Fin M → Str E :=
  fun k => if k = i then z k else thc T (z k)

lemma measurable_sumW₂ (i : Fin M) : Measurable fun p : ℝ × (Fin M → Str E) => sumW i p.1 p.2 := by
  unfold sumW
  refine Finset.measurable_sum _ fun k _ => ?_
  by_cases hk : k = i
  · simp only [if_pos hk]; exact measurable_const
  · simp only [if_neg hk]
    have hf : Measurable fun p : ℝ × (Fin M → Str E) => (p.1, p.2 k) :=
      measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)
    have h2 := measurable_cW₂.comp hf
    exact h2

lemma measurable_rest₂ (i : Fin M) : Measurable fun p : ℝ × (Fin M → Str E) => rest i p.1 p.2 := by
  unfold rest
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k = i
  · simp only [if_pos hk]; exact (measurable_pi_apply k).comp measurable_snd
  · simp only [if_neg hk]
    have hf : Measurable fun p : ℝ × (Fin M → Str E) => (p.1, p.2 k) :=
      measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)
    simpa only [Function.comp_def] using measurable_thc₂.comp hf

/-- the first window of class `i`: (requirement of its first job, the other classes' work in
`[0, T]`, the first arrival time `T`). -/
noncomputable def WinS (i : Fin M) (z : Fin M → Str E) : ℝ × ℝ × ℝ :=
  ((z i).2.1 0, sumW i ((z i).1 0) z, (z i).1 0)

/-- the system seen from class `i`'s first arrival: class `i` loses its first job, the other
classes are restarted at that arrival. -/
noncomputable def thS (i : Fin M) (z : Fin M → Str E) : Fin M → Str E :=
  fun k => if k = i then tailS (z i) else thc ((z i).1 0) (z k)

lemma measurable_tailS : Measurable (tailS (E := E)) :=
  ((measurable_shiftN 1).comp measurable_fst).prodMk
    (((measurable_shiftN 1).comp measurable_snd.fst).prodMk
      ((measurable_shiftN 1).comp measurable_snd.snd))

lemma measurable_T0 (i : Fin M) : Measurable fun z : Fin M → Str E => (z i).1 0 :=
  (measurable_pi_apply 0).comp (measurable_fst.comp (measurable_pi_apply i))

lemma measurable_WinS (i : Fin M) : Measurable (WinS (E := E) i) := by
  have h1 : Measurable fun z : Fin M → Str E => (z i).2.1 0 :=
    (measurable_pi_apply 0).comp (measurable_snd.fst.comp (measurable_pi_apply i))
  have h2 := (measurable_sumW₂ (E := E) i).comp ((measurable_T0 i).prodMk measurable_id)
  exact h1.prodMk (h2.prodMk (measurable_T0 i))

lemma measurable_thS (i : Fin M) : Measurable (thS (E := E) i) := by
  unfold thS
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k = i
  · simp only [if_pos hk]; exact measurable_tailS.comp (measurable_pi_apply i)
  · simp only [if_neg hk]
    have h2 := (measurable_thc₂ (E := E)).comp ((measurable_T0 i).prodMk (measurable_pi_apply k))
    exact h2

lemma WinS_split (i : Fin M) (h : ℝ × ℝ × E) (y : Fin M → Str E) :
    WinS i (update y i (consS h (y i))) = (h.2.1, sumW i h.1 y, h.1) := by
  classical
  simp only [WinS, update_self]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  show sumW i h.1 _ = sumW i h.1 y
  unfold sumW
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · simp [hk]
  · simp [hk, update_of_ne hk]

lemma thS_split (i : Fin M) (h : ℝ × ℝ × E) (y : Fin M → Str E) :
    thS i (update y i (consS h (y i))) = rest i h.1 y := by
  classical
  funext k
  by_cases hk : k = i
  · subst hk; simp [thS, rest]
  · simp [thS, rest, hk, update_of_ne hk]; rfl

lemma ae_pos_exp (r : ℝ) : ∀ᵐ y ∂(expMeasure r), 0 < y := by
  rw [ae_iff]
  simp only [not_lt]
  unfold expMeasure gammaMeasure
  show (volume.withDensity (gammaPDF 1 r)) (Set.Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

section Restart
variable (lam : Fin M → ℝ) [∀ k, IsProbabilityMeasure (expMeasure (lam k))]
  (β : Fin M → Measure ℝ) [∀ k, IsProbabilityMeasure (β k)] (η : Measure E) [IsProbabilityMeasure η]

/-- the class laws. -/
noncomputable abbrev QQ (k : Fin M) : Measure (Str E) := Qs (expMeasure (lam k)) (β k) η

/-- the law of the work class `k` brings in `[0, T]` (none for class `i`). -/
noncomputable def CT (i : Fin M) (T : ℝ) (k : Fin M) : Measure ℝ :=
  if k = i then Measure.dirac 0 else (QQ lam β η k).map (cW T)

instance (i : Fin M) (T : ℝ) (k : Fin M) : IsProbabilityMeasure (CT lam β η i T k) := by
  unfold CT
  split_ifs
  · infer_instance
  · exact Measure.isProbabilityMeasure_map (measurable_cW T).aemeasurable

lemma map_fk (hlam : ∀ k, 0 < lam k) (i : Fin M) {T : ℝ} (hT : 0 ≤ T) (k : Fin M) :
    (QQ lam β η k).map (fk i T k) = (CT lam β η i T k).prod (QQ lam β η k) := by
  by_cases hk : k = i
  · have : fk (E := E) i T k = Prod.mk 0 := by funext s; simp [fk, hk]
    rw [this, CT, if_pos hk, Measure.dirac_prod]
  · have : fk (E := E) i T k = fun s => (cW T s, thc T s) := by funext s; simp [fk, hk]
    rw [this, CT, if_neg hk]
    exact map_cW_thc (β k) η (hlam k) hT

/-- **restart.** For a deterministic `T ≥ 0`, the other classes' work in `[0, T]` is independent
of the restarted system, which has the original law. -/
theorem map_restart (hlam : ∀ k, 0 < lam k) (i : Fin M) {T : ℝ} (hT : 0 ≤ T) :
    (Measure.pi (QQ lam β η)).map (fun z => (sumW i T z, rest i T z)) =
      ((Measure.pi (CT lam β η i T)).map (fun c => ∑ k, c k)).prod (Measure.pi (QQ lam β η)) := by
  haveI : ∀ k, SigmaFinite ((QQ lam β η k).map (fk i T k)) := fun k => by
    rw [map_fk lam β η hlam i hT k]; infer_instance
  have h1 := Measure.pi_map_pi (μ := QQ lam β η) (f := fun k => fk i T k)
    (fun k => (measurable_fk i T k).aemeasurable)
  simp_rw [map_fk lam β η hlam i hT] at h1
  have h2 := (measurePreserving_arrowProdEquivProdArrow ℝ (Str E) (Fin M) (CT lam β η i T)
    (QQ lam β η)).map_eq
  have h3 : Measurable fun c : Fin M → ℝ => ∑ k, c k :=
    Finset.measurable_sum _ fun k _ => measurable_pi_apply k
  have hΦ : Measurable fun z : Fin M → Str E => fun k => fk i T k (z k) :=
    measurable_pi_lambda _ fun k => (measurable_fk i T k).comp (measurable_pi_apply k)
  have e : (fun z : Fin M → Str E => (sumW i T z, rest i T z)) =
      Prod.map (fun c : Fin M → ℝ => ∑ k, c k) id ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Str E) (Fin M)) ∘
          (fun z k => fk i T k (z k)) := by
    funext z
    refine Prod.ext ?_ ?_
    · show (∑ k, if k = i then (0 : ℝ) else cW T (z k)) = ∑ k, (fk i T k (z k)).1
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i <;> simp [fk, hk]
    · funext k
      by_cases hk : k = i <;> simp [fk, rest, hk, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
  rw [e, ← Measure.map_map (h3.prodMap measurable_id) ((MeasurableEquiv.measurable _).comp hΦ),
    ← Measure.map_map (MeasurableEquiv.measurable _) hΦ, h1, h2,
    ← Measure.map_prod_map _ _ h3 measurable_id, Measure.map_id]

/-- **P2b-2 (stream level).** The first window of class `i` is independent of the system seen
from class `i`'s first arrival, and that system has the original law. -/
theorem map_win_theta (hlam : ∀ k, 0 < lam k) (i : Fin M) :
    (Measure.pi (QQ lam β η)).map (fun z => (WinS i z, thS i z)) =
      ((Measure.pi (QQ lam β η)).map (WinS i)).prod (Measure.pi (QQ lam β η)) := by
  classical
  set ν := Measure.pi (QQ lam β η) with hν
  set H := Hs (expMeasure (lam i)) (β i) η with hH
  have hsplit : (H.prod ν).map (fun p => update p.2 i (consS p.1 (p.2 i))) = ν :=
    map_split (QQ lam β η) i H (map_consS _ _ _)
  have hΨ : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
      update p.2 i (consS p.1 (p.2 i)) :=
    measurable_update'.comp (measurable_snd.prodMk
      (measurable_consS.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))
  have key : ∀ S, MeasurableSet S →
      ν S = (H.prod ν) ((fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
        update p.2 i (consS p.1 (p.2 i))) ⁻¹' S) := by
    intro S hS
    conv_lhs => rw [← hsplit]
    rw [Measure.map_apply hΨ hS]
  have hae : ∀ᵐ h ∂H, 0 ≤ h.1 := by
    have := (measurePreserving_fst (μ := expMeasure (lam i)) (ν := (β i).prod η)).quasiMeasurePreserving.ae
      (ae_pos_exp (lam i))
    filter_upwards [this] with h hh using hh.le
  haveI : IsProbabilityMeasure (ν.map (WinS i)) :=
    Measure.isProbabilityMeasure_map (measurable_WinS i).aemeasurable
  have hF : Measurable fun z : Fin M → Str E => (WinS i z, thS i z) :=
    (measurable_WinS i).prodMk (measurable_thS i)
  have hS2 : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) => sumW i p.1.1 p.2 := by
    have h := (measurable_sumW₂ (E := E) i).comp (measurable_fst.fst.prodMk measurable_snd :
      Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) => (p.1.1, p.2))
    exact h
  have hR2 : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) => rest i p.1.1 p.2 := by
    have h := (measurable_rest₂ (E := E) i).comp (measurable_fst.fst.prodMk measurable_snd :
      Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) => (p.1.1, p.2))
    exact h
  have G2m : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
      (p.1.2.1, sumW i p.1.1 p.2, p.1.1) :=
    measurable_fst.snd.fst.prodMk (hS2.prodMk measurable_fst.fst)
  have G1m : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
      ((p.1.2.1, sumW i p.1.1 p.2, p.1.1), rest i p.1.1 p.2) := G2m.prodMk hR2
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply hF (hA.prod hB), Measure.map_apply (measurable_WinS i) hA,
    key _ (hF (hA.prod hB)), key _ (measurable_WinS i hA)]
  have e1 : (fun p : (ℝ × ℝ × E) × (Fin M → Str E) => update p.2 i (consS p.1 (p.2 i))) ⁻¹'
      ((fun z => (WinS i z, thS i z)) ⁻¹' (A ×ˢ B)) =
      (fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
        ((p.1.2.1, sumW i p.1.1 p.2, p.1.1), rest i p.1.1 p.2)) ⁻¹' (A ×ˢ B) := by
    ext p; simp only [mem_preimage, WinS_split, thS_split]
  have e2 : (fun p : (ℝ × ℝ × E) × (Fin M → Str E) => update p.2 i (consS p.1 (p.2 i))) ⁻¹'
      (WinS i ⁻¹' A) =
      (fun p : (ℝ × ℝ × E) × (Fin M → Str E) => (p.1.2.1, sumW i p.1.1 p.2, p.1.1)) ⁻¹' A := by
    ext p; simp only [mem_preimage, WinS_split]
  rw [e1, e2, Measure.prod_apply (G1m (hA.prod hB)), Measure.prod_apply (G2m hA),
    ← lintegral_mul_const' _ _ (measure_ne_top ν B)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with h hh
  have hR := map_restart lam β η hlam i hh
  have hm2 : Measurable fun y : Fin M → Str E => (sumW i h.1 y, rest i h.1 y) := by
    have h1 := (measurable_sumW₂ (E := E) i).comp (measurable_const.prodMk measurable_id
      : Measurable fun y : Fin M → Str E => (h.1, y))
    have h2 := (measurable_rest₂ (E := E) i).comp (measurable_const.prodMk measurable_id
      : Measurable fun y : Fin M → Str E => (h.1, y))
    exact h1.prodMk h2
  have hSl : MeasurableSet {c : ℝ | (h.2.1, c, h.1) ∈ A} :=
    (measurable_const.prodMk (measurable_id.prodMk measurable_const)) hA
  have l1 : Prod.mk h ⁻¹' ((fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
        ((p.1.2.1, sumW i p.1.1 p.2, p.1.1), rest i p.1.1 p.2)) ⁻¹' (A ×ˢ B)) =
      (fun y => (sumW i h.1 y, rest i h.1 y)) ⁻¹' ({c : ℝ | (h.2.1, c, h.1) ∈ A} ×ˢ B) := by
    ext y; simp only [mem_preimage, mem_prod, mem_setOf_eq]
  have l2 : Prod.mk h ⁻¹' ((fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
        (p.1.2.1, sumW i p.1.1 p.2, p.1.1)) ⁻¹' A) =
      (fun y => (sumW i h.1 y, rest i h.1 y)) ⁻¹' ({c : ℝ | (h.2.1, c, h.1) ∈ A} ×ˢ univ) := by
    ext y; simp only [mem_preimage, mem_prod, mem_setOf_eq, mem_univ, and_true]
  rw [l1, l2, ← Measure.map_apply hm2 (hSl.prod hB),
    ← Measure.map_apply hm2 (hSl.prod MeasurableSet.univ), hR, Measure.prod_prod,
    Measure.prod_prod, measure_univ, mul_one]

/-- the law of class `i`'s first window: `(r, A, τ)` with `(r, τ)` the first job of class `i` and
`A` the other classes' work in `[0, τ]` (for P4's moment computations). -/
theorem law_WinS (i : Fin M) :
    (Measure.pi (QQ lam β η)).map (WinS i) =
      ((Hs (expMeasure (lam i)) (β i) η).prod (Measure.pi (QQ lam β η))).map
        (fun p => (p.1.2.1, sumW i p.1.1 p.2, p.1.1)) := by
  classical
  have hsplit := map_split (QQ lam β η) i (Hs (expMeasure (lam i)) (β i) η) (map_consS _ _ _)
  have hΨ : Measurable fun p : (ℝ × ℝ × E) × (Fin M → Str E) =>
      update p.2 i (consS p.1 (p.2 i)) :=
    measurable_update'.comp (measurable_snd.prodMk
      (measurable_consS.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))
  conv_lhs => rw [← hsplit]
  rw [Measure.map_map (measurable_WinS i) hΨ]
  congr 1
  funext p
  exact WinS_split i p.1 p.2

end Restart

end Streams

/-! ### i.i.d. windows from a one-step independence -/

section IidWindows
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X)
  [IsProbabilityMeasure ν] {W : X → Y} {θ : X → X}

lemma iter_rect (hW : Measurable W) (hθ : Measurable θ)
    (hind : ν.map (fun x => (W x, θ x)) = (ν.map W).prod ν) (N : ℕ) :
    ∀ (t : ℕ → Set Y), (∀ n, MeasurableSet (t n)) → ∀ B : Set X, MeasurableSet B →
      ν {x | (∀ n < N, W (θ^[n] x) ∈ t n) ∧ θ^[N] x ∈ B} =
        (∏ n ∈ Finset.range N, (ν.map W) (t n)) * ν B := by
  haveI : IsProbabilityMeasure (ν.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  induction N with
  | zero =>
    intro t _ B _
    simp
  | succ N ih =>
    intro t ht B hB
    have hS : MeasurableSet {w | (∀ n < N, W (θ^[n] w) ∈ t (n + 1)) ∧ θ^[N] w ∈ B} := by
      have : {w | (∀ n < N, W (θ^[n] w) ∈ t (n + 1)) ∧ θ^[N] w ∈ B} =
          (⋂ n ∈ Finset.range N, (W ∘ θ^[n]) ⁻¹' t (n + 1)) ∩ θ^[N] ⁻¹' B := by
        ext w; simp
      rw [this]
      exact (Finset.measurableSet_biInter _ fun n _ => (hW.comp (hθ.iterate n)) (ht (n + 1))).inter
        ((hθ.iterate N) hB)
    have e : {x | (∀ n < N + 1, W (θ^[n] x) ∈ t n) ∧ θ^[N + 1] x ∈ B} =
        (fun x => (W x, θ x)) ⁻¹'
          (t 0 ×ˢ {w | (∀ n < N, W (θ^[n] w) ∈ t (n + 1)) ∧ θ^[N] w ∈ B}) := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_preimage, mem_prod, iterate_succ_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by simpa using h1 0 (Nat.succ_pos N),
          fun n hn => by simpa [iterate_succ_apply] using h1 (n + 1) (by omega), h2⟩
      · rintro ⟨h0, h1, h2⟩
        refine ⟨fun n hn => ?_, h2⟩
        cases n with
        | zero => simpa using h0
        | succ n => simpa [iterate_succ_apply] using h1 n (by omega)
    rw [e, ← Measure.map_apply (hW.prodMk hθ) ((ht 0).prod hS), hind, Measure.prod_prod,
      ih (fun n => t (n + 1)) (fun n => ht (n + 1)) B hB, Finset.prod_range_succ']
    ring

/-- **i.i.d. windows.** If the window `W` is independent of the shifted point `θ x`, which has
the original law, then the windows along the orbit of `θ` are i.i.d. -/
theorem map_orbit_iid (hW : Measurable W) (hθ : Measurable θ)
    (hind : ν.map (fun x => (W x, θ x)) = (ν.map W).prod ν) :
    haveI : IsProbabilityMeasure (ν.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
    ν.map (fun x n => W (θ^[n] x)) = Measure.infinitePi fun _ : ℕ => ν.map W := by
  classical
  haveI : IsProbabilityMeasure (ν.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hF : Measurable fun x n => W (θ^[n] x) :=
    measurable_pi_lambda _ fun n => hW.comp (hθ.iterate n)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hF (MeasurableSet.pi s.countable_toSet fun n _ => ht n)]
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N :=
    ⟨s.sup id + 1, fun n hn => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  let t' : ℕ → Set Y := fun n => if n ∈ s then t n else univ
  have ht' : ∀ n, MeasurableSet (t' n) := fun n => by
    by_cases hn : n ∈ s
    · simp only [t', if_pos hn]; exact ht n
    · simp only [t', if_neg hn]; exact MeasurableSet.univ
  have e : (fun x n => W (θ^[n] x)) ⁻¹' Set.pi (↑s) t =
      {x | (∀ n < N, W (θ^[n] x) ∈ t' n) ∧ θ^[N] x ∈ (univ : Set X)} := by
    ext x
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_ofPred_eq, mem_univ, and_true]
    constructor
    · intro h n _
      by_cases hn : n ∈ s
      · simp only [t', if_pos hn]; exact h n hn
      · simp only [t', if_neg hn]; exact mem_univ _
    · intro h n hn
      have := h n (Finset.mem_range.1 (hN hn))
      simpa only [t', if_pos hn] using this
  rw [e, iter_rect ν hW hθ hind N t' ht' univ MeasurableSet.univ, measure_univ, mul_one]
  calc ∏ n ∈ Finset.range N, (ν.map W) (t' n) = ∏ n ∈ s, (ν.map W) (t' n) :=
        (Finset.prod_subset hN fun n _ hn => by simp only [t', if_neg hn, measure_univ]).symm
    _ = ∏ n ∈ s, (ν.map W) (t n) := Finset.prod_congr rfl fun n hn => by simp only [t', if_pos hn]

end IidWindows

/-! ### back on the multi-class sample space -/

section OmegaLevel
variable {M : ℕ} {E : Type*} [MeasurableSpace E]
  (lam : Fin M → ℝ) [∀ k, IsProbabilityMeasure (expMeasure (lam k))]
  (β : Fin M → Measure ℝ) [∀ k, IsProbabilityMeasure (β k)] (η : Measure E) [IsProbabilityMeasure η]

/-- the shift to class `i`'s first arrival, on the sample space. -/
noncomputable def thO (i : Fin M) (ω : Om M E) : Om M E := ofS (thS i (toS ω))

/-- class `i`'s first window, on the sample space. -/
noncomputable def WinO (i : Fin M) (ω : Om M E) : ℝ × ℝ × ℝ := WinS i (toS ω)

lemma measurable_thO (i : Fin M) : Measurable (thO (M := M) (E := E) i) :=
  measurable_ofS.comp ((measurable_thS i).comp measurable_toS)

lemma measurable_WinO (i : Fin M) : Measurable (WinO (M := M) (E := E) i) :=
  (measurable_WinS i).comp measurable_toS

theorem map_toS' : (PO (fun k => expMeasure (lam k)) β η).map toS = Measure.pi (QQ lam β η) :=
  map_toS _ _ _

theorem map_ofS : (Measure.pi (QQ lam β η)).map ofS = PO (fun k => expMeasure (lam k)) β η := by
  rw [← map_toS' lam β η, Measure.map_map measurable_ofS measurable_toS]
  exact Measure.map_id

/-- **P2b-2.** -/
theorem map_winO_thO (hlam : ∀ k, 0 < lam k) (i : Fin M) :
    (PO (fun k => expMeasure (lam k)) β η).map (fun ω => (WinO i ω, thO i ω)) =
      ((PO (fun k => expMeasure (lam k)) β η).map (WinO i)).prod
        (PO (fun k => expMeasure (lam k)) β η) := by
  have e1 : (fun ω : Om M E => (WinO i ω, thO i ω)) =
      Prod.map id ofS ∘ (fun z => (WinS i z, thS i z)) ∘ toS := rfl
  have e2 : (WinO (M := M) (E := E) i) = WinS i ∘ toS := rfl
  have hF : Measurable fun z : Fin M → Str E => (WinS i z, thS i z) :=
    (measurable_WinS i).prodMk (measurable_thS i)
  rw [e1, e2, ← Measure.map_map (measurable_id.prodMap measurable_ofS) (hF.comp measurable_toS),
    ← Measure.map_map hF measurable_toS, ← Measure.map_map (measurable_WinS i) measurable_toS,
    map_toS' lam β η, map_win_theta lam β η hlam i]
  haveI : IsProbabilityMeasure ((Measure.pi (QQ lam β η)).map (WinS i)) :=
    Measure.isProbabilityMeasure_map (measurable_WinS i).aemeasurable
  rw [← Measure.map_prod_map _ _ measurable_id measurable_ofS, Measure.map_id, map_ofS]

/-- **P2b-3.** The windows of class `i` along the orbit of the shift are i.i.d. -/
theorem map_windows_iid (hlam : ∀ k, 0 < lam k) (i : Fin M) :
    haveI : IsProbabilityMeasure ((PO (fun k => expMeasure (lam k)) β η).map (WinO i)) :=
      Measure.isProbabilityMeasure_map (measurable_WinO i).aemeasurable
    (PO (fun k => expMeasure (lam k)) β η).map (fun ω n => WinO i ((thO i)^[n] ω)) =
      Measure.infinitePi fun _ : ℕ => (PO (fun k => expMeasure (lam k)) β η).map (WinO i) :=
  map_orbit_iid _ (measurable_WinO i) (measurable_thO i) (map_winO_thO lam β η hlam i)

/-- the shift preserves the law. -/
theorem map_thO (hlam : ∀ k, 0 < lam k) (i : Fin M) :
    (PO (fun k => expMeasure (lam k)) β η).map (thO i) = PO (fun k => expMeasure (lam k)) β η := by
  have h := congrArg (fun μ => μ.map Prod.snd) (map_winO_thO lam β η hlam i)
  haveI : IsProbabilityMeasure ((PO (fun k => expMeasure (lam k)) β η).map (WinO i)) :=
    Measure.isProbabilityMeasure_map (measurable_WinO i).aemeasurable
  rw [Measure.map_map measurable_snd ((measurable_WinO i).prodMk (measurable_thO i)),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

end OmegaLevel

end CMT


/-! ## P4 (part 1): moments of one exponential stream (Mathlib only, laptop iteration).
`x : ℕ → ℝ` i.i.d. `Exp r`; `CMR.psum x m` is the time of arrival `m - 1`; `CMR.Nidx t x` is the
number of arrivals in `[0, t]`. Results: the Laplace transform of `psum`, a Chernoff bound for
`psum ≤ t`, and Wald's identity `E N_t = r t`. -/

namespace CMU
open MeasureTheory ProbabilityTheory Set

/-- the exponential law's moment generating function, `ENNReal` form. -/
lemma lintegral_exp_mul_expMeasure {r c : ℝ} (hr : 0 < r) (hc : c < r) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂(expMeasure r) = ENNReal.ofReal (r / (r - c)) := by
  have hm : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (c * x)) := by fun_prop
  show ∫⁻ x, _ ∂(volume.withDensity (gammaPDF 1 r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hf]
  have heq : (gammaPDF 1 r * fun x => ENNReal.ofReal (Real.exp (c * x))) =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (r * Real.exp ((c - r) * x))) := by
    funext x
    simp only [Pi.mul_apply]
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), CMR.gammaPDF_one_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), gammaPDF_of_neg (lt_of_not_ge hx),
        zero_mul]
  have hcr : c - r < 0 := by linarith
  rw [heq, lintegral_indicator measurableSet_Ici, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi hcr 0]
    congr 1
    have : r - c ≠ 0 := by linarith
    field_simp
    simp
    rw [show c - r = -(r - c) by ring, div_neg, neg_neg, div_self this]
  · exact Integrable.const_mul ((integrableOn_exp_mul_Ioi hcr 0).congr_set_ae Ioi_ae_eq_Ici.symm) r
  · exact ae_of_all _ fun x => by positivity

/-- the mean of the exponential law, `ENNReal` form. -/
lemma lintegral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  obtain ⟨hi, he⟩ := CMS.expMeasure_mean hr
  have hpos : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
    filter_upwards [CMT.ae_pos_exp r] with x hx using hx.le
  have h1 := ofReal_integral_eq_lintegral_ofReal hi hpos
  simp only [id_eq] at h1
  rw [← he, h1]

section Stream
variable {r : ℝ} [IsProbabilityMeasure (expMeasure r)]

/-- the i.i.d. law of one stream. -/
noncomputable abbrev nu (r : ℝ) [IsProbabilityMeasure (expMeasure r)] : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => expMeasure r

lemma lintegral_eval_nu {h : ℝ → ENNReal} (hh : Measurable h) (m : ℕ) :
    ∫⁻ x, h (x m) ∂(nu r) = ∫⁻ y, h y ∂(expMeasure r) := by
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure r) m,
    lintegral_map hh (measurable_pi_apply m)]

/-- Laplace transform of the arrival times. -/
theorem lintegral_exp_psum (hr : 0 < r) {c : ℝ} (hc : c < r) (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * CMR.psum x k)) ∂(nu r)
      = ENNReal.ofReal (r / (r - c)) ^ k := by
  induction k with
  | zero => simp [CMR.psum]
  | succ k ih =>
    have hmeas : Measurable fun x : ℕ → ℝ => ENNReal.ofReal (Real.exp (c * CMR.psum x (k + 1))) :=
      (((CMR.measurable_psum (k + 1)).const_mul c).exp).ennreal_ofReal
    rw [nu, ← CMR.map_consN (expMeasure r), lintegral_map hmeas CMR.measurable_consN]
    have hpt : ∀ p : ℝ × (ℕ → ℝ),
        ENNReal.ofReal (Real.exp (c * CMR.psum (CMR.consN p.1 p.2) (k + 1)))
          = ENNReal.ofReal (Real.exp (c * p.1)) * ENNReal.ofReal (Real.exp (c * CMR.psum p.2 k)) := by
      intro p
      rw [CMR.psum_consN, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp_rw [hpt]
    rw [lintegral_prod_mul (f := fun a : ℝ => ENNReal.ofReal (Real.exp (c * a)))
      (g := fun x : ℕ → ℝ => ENNReal.ofReal (Real.exp (c * CMR.psum x k)))
      ((measurable_id.const_mul c).exp.ennreal_ofReal).aemeasurable
      (((CMR.measurable_psum k).const_mul c).exp.ennreal_ofReal).aemeasurable,
      lintegral_exp_mul_expMeasure hr hc, ← nu, ih, pow_succ, mul_comm]

/-- Chernoff bound for the arrival times. -/
theorem meas_psum_le (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (k : ℕ) :
    (nu r) {x | CMR.psum x k ≤ t}
      ≤ ENNReal.ofReal (Real.exp (s * t)) * ENNReal.ofReal (r / (r + s)) ^ k := by
  have hms : MeasurableSet {x : ℕ → ℝ | CMR.psum x k ≤ t} :=
    measurableSet_le (CMR.measurable_psum k) measurable_const
  have hL := lintegral_exp_psum hr (c := -s) (by linarith) k
  rw [show r - -s = r + s by ring] at hL
  rw [← lintegral_indicator_one hms, ← hL,
    ← lintegral_const_mul _ (((CMR.measurable_psum k).const_mul (-s)).exp.ennreal_ofReal)]
  refine lintegral_mono fun x => ?_
  by_cases hx : CMR.psum x k ≤ t
  · rw [indicator_of_mem (show x ∈ {x : ℕ → ℝ | CMR.psum x k ≤ t} from hx), Pi.one_apply,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (by nlinarith)
  · rw [indicator_of_notMem (show x ∉ {x : ℕ → ℝ | CMR.psum x k ≤ t} from hx)]
    exact bot_le

/-- the indicator of `psum ≤ t`. -/
noncomputable def ind (t : ℝ) (p : ℝ) : ENNReal := (Iic t).indicator 1 p

lemma measurable_ind (t : ℝ) : Measurable (ind t) :=
  measurable_one.indicator measurableSet_Iic

lemma ind_add (t a p : ℝ) : ind t (a + p) = ind (t - a) p := by
  unfold ind
  by_cases h : a + p ≤ t
  · rw [indicator_of_mem (show a + p ∈ Iic t from h),
      indicator_of_mem (show p ∈ Iic (t - a) from by simp only [mem_Iic]; linarith)]
    rfl
  · rw [indicator_of_notMem (show a + p ∉ Iic t from h),
      indicator_of_notMem (show p ∉ Iic (t - a) from by simp only [mem_Iic]; intro h'; apply h; linarith)]

/-- the coordinate `x m` is independent of the arrival time `psum x m` (Wald's key step). -/
theorem lintegral_coord_ind (hr : 0 < r) {h : ℝ → ENNReal} (hh : Measurable h) (m : ℕ) :
    ∀ t : ℝ, ∫⁻ x, h (x m) * ind t (CMR.psum x m) ∂(nu r)
      = (∫⁻ y, h y ∂(expMeasure r)) * ∫⁻ x, ind t (CMR.psum x m) ∂(nu r) := by
  induction m with
  | zero =>
    intro t
    simp only [CMR.psum, Finset.range_zero, Finset.sum_empty]
    have hm0 : Measurable fun x : ℕ → ℝ => h (x 0) := hh.comp (measurable_pi_apply 0)
    rw [lintegral_mul_const _ hm0, lintegral_eval_nu hh 0,
      lintegral_const, measure_univ, mul_one]
  | succ m ih =>
    intro t
    have hm1 : Measurable fun x : ℕ → ℝ => h (x (m + 1)) * ind t (CMR.psum x (m + 1)) :=
      (hh.comp (measurable_pi_apply _)).mul ((measurable_ind t).comp (CMR.measurable_psum _))
    have hm2 : Measurable fun x : ℕ → ℝ => ind t (CMR.psum x (m + 1)) :=
      (measurable_ind t).comp (CMR.measurable_psum _)
    rw [nu, ← CMR.map_consN (expMeasure r), lintegral_map hm1 CMR.measurable_consN,
      lintegral_map hm2 CMR.measurable_consN]
    simp only [CMR.consN_succ, CMR.psum_consN, ind_add]
    have hj1 : Measurable fun p : ℝ × (ℕ → ℝ) => h (p.2 m) * ind (t - p.1) (CMR.psum p.2 m) := by
      have : Measurable fun p : ℝ × (ℕ → ℝ) => ind (t - p.1) (CMR.psum p.2 m) := by
        have e : (fun p : ℝ × (ℕ → ℝ) => ind (t - p.1) (CMR.psum p.2 m)) =
            fun p => ind t (p.1 + CMR.psum p.2 m) := by
          funext p; rw [ind_add]
        rw [e]
        exact (measurable_ind t).comp (measurable_fst.add ((CMR.measurable_psum m).comp measurable_snd))
      exact (hh.comp ((measurable_pi_apply m).comp measurable_snd)).mul this
    have hj2 : Measurable fun p : ℝ × (ℕ → ℝ) => ind (t - p.1) (CMR.psum p.2 m) := by
      have e : (fun p : ℝ × (ℕ → ℝ) => ind (t - p.1) (CMR.psum p.2 m)) =
          fun p => ind t (p.1 + CMR.psum p.2 m) := by
        funext p; rw [ind_add]
      rw [e]
      exact (measurable_ind t).comp (measurable_fst.add ((CMR.measurable_psum m).comp measurable_snd))
    rw [lintegral_prod _ hj1.aemeasurable, ← lintegral_const_mul _ hj2,
      lintegral_prod _ (hj2.const_mul _).aemeasurable]
    refine lintegral_congr fun a => ?_
    rw [← nu, ih (t - a)]
    exact (lintegral_const_mul _ ((measurable_ind _).comp (CMR.measurable_psum m))).symm

lemma psum_mono {x : ℕ → ℝ} (hx : ∀ m, 0 ≤ x m) {a b : ℕ} (hab : a ≤ b) :
    CMR.psum x a ≤ CMR.psum x b := by
  unfold CMR.psum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun m _ _ => hx m

/-- on `Ev t N x`, the indicator `psum x m ≤ t` is `m ≤ N`. -/
lemma ind_psum_eq {t : ℝ} (ht : 0 ≤ t) {x : ℕ → ℝ} (hx : ∀ m, 0 ≤ x m) {N : ℕ}
    (hE : CMR.Ev t N x) (m : ℕ) :
    ind t (CMR.psum x m) = if m ≤ N then 1 else 0 := by
  unfold ind
  split_ifs with hm
  · apply indicator_of_mem
    simp only [mem_Iic]
    rcases m with _ | j
    · simp [CMR.psum, ht]
    · exact hE.1 j (by omega)
  · apply indicator_of_notMem
    simp only [mem_Iic, not_le]
    exact lt_of_lt_of_le hE.2 (psum_mono hx (by omega))

lemma ae_nonneg_nu (hr : 0 < r) : ∀ᵐ x ∂(nu r), ∀ m, 0 ≤ x m := by
  rw [ae_all_iff]
  intro m
  have h := CMT.ae_pos_exp (r := r)
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure r) m] at h
  filter_upwards [ae_of_ae_map (measurable_pi_apply m).aemeasurable h] with x hx using hx.le

/-- **Wald's identity** for the Poisson count: `E N_t = r t`. -/
theorem lintegral_Nidx (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x, (CMR.Nidx t x : ENNReal) ∂(nu r) = ENNReal.ofReal (r * t) := by
  have hEv := CMR.ae_exists_Ev hr ht
  have hnn := ae_nonneg_nu (r := r) hr
  -- the pathwise identities
  have hgood : ∀ᵐ x ∂(nu r), CMR.Ev t (CMR.Nidx t x) x ∧ ∀ m, 0 ≤ x m := by
    filter_upwards [hEv, hnn] with x ⟨k, hk⟩ h0
    exact ⟨by rw [CMR.Nidx_eq hk]; exact hk, h0⟩
  have hsum1 : ∀ᵐ x ∂(nu r), ENNReal.ofReal (CMR.psum x (CMR.Nidx t x + 1)) =
      ∑' m, ENNReal.ofReal (x m) * ind t (CMR.psum x m) := by
    filter_upwards [hgood] with x ⟨hE, h0⟩
    simp_rw [ind_psum_eq ht h0 hE]
    rw [tsum_eq_sum (s := Finset.range (CMR.Nidx t x + 1)) (fun m hm => by
      rw [Finset.mem_range] at hm; simp only [if_neg (show ¬ m ≤ CMR.Nidx t x by omega), mul_zero])]
    rw [CMR.psum, ENNReal.ofReal_sum_of_nonneg (fun m _ => h0 m)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [if_pos (by omega), mul_one]
  have hsum2 : ∀ᵐ x ∂(nu r), (CMR.Nidx t x : ENNReal) + 1 = ∑' m, ind t (CMR.psum x m) := by
    filter_upwards [hgood] with x ⟨hE, h0⟩
    simp_rw [ind_psum_eq ht h0 hE]
    rw [tsum_eq_sum (s := Finset.range (CMR.Nidx t x + 1)) (fun m hm => by
      rw [Finset.mem_range] at hm; exact if_neg (by omega))]
    rw [Finset.sum_ite_of_true (fun m hm => by rw [Finset.mem_range] at hm; omega)]
    simp
  have hmi : ∀ m, Measurable fun x : ℕ → ℝ => ind t (CMR.psum x m) := fun m =>
    (measurable_ind t).comp (CMR.measurable_psum m)
  -- the left side: `psum (N + 1) = t + residual`
  have hres : ∀ x, CMR.psum x (CMR.Nidx t x + 1) = t + CMR.post t x 0 := by
    intro x; simp [CMR.post, CMR.postK]
  have hL : ∫⁻ x, ENNReal.ofReal (CMR.psum x (CMR.Nidx t x + 1)) ∂(nu r)
      = ENNReal.ofReal t + ENNReal.ofReal (1 / r) := by
    have hpost : ∀ᵐ x ∂(nu r), 0 ≤ CMR.post t x 0 := by
      filter_upwards [hgood] with x ⟨hE, _⟩
      linarith [hres x, hE.2]
    rw [lintegral_congr_ae (by filter_upwards [hpost] with x hx using
      (show ENNReal.ofReal (CMR.psum x (CMR.Nidx t x + 1)) =
        ENNReal.ofReal t + ENNReal.ofReal (CMR.post t x 0) by rw [hres, ENNReal.ofReal_add ht hx]))]
    have hmp : Measurable fun x : ℕ → ℝ => ENNReal.ofReal (CMR.post t x 0) :=
      ((measurable_pi_apply 0).comp (CMR.measurable_post t)).ennreal_ofReal
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    congr 1
    have h1 : ∫⁻ x, ENNReal.ofReal (CMR.post t x 0) ∂(nu r)
        = ∫⁻ y, ENNReal.ofReal (y 0) ∂((nu r).map (CMR.post t)) := by
      rw [lintegral_map ((measurable_pi_apply 0).ennreal_ofReal) (CMR.measurable_post t)]
    rw [h1, nu, CMR.map_post hr ht, ← nu,
      lintegral_eval_nu (h := ENNReal.ofReal) ENNReal.measurable_ofReal 0, lintegral_id_expMeasure hr]
  -- the right side: Wald
  have hR : ∫⁻ x, ENNReal.ofReal (CMR.psum x (CMR.Nidx t x + 1)) ∂(nu r)
      = ENNReal.ofReal (1 / r) * ((∫⁻ x, (CMR.Nidx t x : ENNReal) ∂(nu r)) + 1) := by
    rw [lintegral_congr_ae hsum1, lintegral_tsum (fun m =>
      (show Measurable fun x : ℕ → ℝ => ENNReal.ofReal (x m) * ind t (CMR.psum x m) from
        (ENNReal.measurable_ofReal.comp (measurable_pi_apply m)).mul (hmi m)).aemeasurable)]
    simp_rw [lintegral_coord_ind hr ENNReal.measurable_ofReal _ t, lintegral_id_expMeasure hr]
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum (fun m => (hmi m).aemeasurable),
      ← lintegral_congr_ae hsum2, lintegral_add_right _ measurable_const, lintegral_const,
      measure_univ, mul_one]
  have key := hL.symm.trans hR
  have hr1 : ENNReal.ofReal r * ENNReal.ofReal (1 / r) = 1 := by
    rw [← ENNReal.ofReal_mul hr.le, mul_one_div_cancel hr.ne', ENNReal.ofReal_one]
  have key2 := congrArg (fun z => ENNReal.ofReal r * z) key
  simp only [mul_add, ← mul_assoc, hr1, one_mul] at key2
  rw [← ENNReal.ofReal_mul hr.le] at key2
  exact ((ENNReal.add_left_inj ENNReal.one_ne_top).1 key2).symm

/-- `E ∏_{m<n} f(x m) = (E f)^n` for an i.i.d. sequence. -/
theorem lintegral_prod_range {α : Type*} [MeasurableSpace α] (ν0 : Measure α)
    [IsProbabilityMeasure ν0] {f : α → ENNReal} (hf : Measurable f) (n : ℕ) :
    ∫⁻ x, ∏ m ∈ Finset.range n, f (x m) ∂(Measure.infinitePi fun _ : ℕ => ν0)
      = (∫⁻ a, f a ∂ν0) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : Measurable fun x : ℕ → α => ∏ m ∈ Finset.range (n + 1), f (x m) :=
      Finset.measurable_prod _ fun m _ => hf.comp (measurable_pi_apply m)
    have hm' : Measurable fun x : ℕ → α => ∏ m ∈ Finset.range n, f (x m) :=
      Finset.measurable_prod _ fun m _ => hf.comp (measurable_pi_apply m)
    rw [← CMR.map_consN ν0, lintegral_map hm CMR.measurable_consN]
    have hpt : ∀ p : α × (ℕ → α), ∏ m ∈ Finset.range (n + 1), f (CMR.consN p.1 p.2 m)
        = f p.1 * ∏ m ∈ Finset.range n, f (p.2 m) := by
      intro p; rw [Finset.prod_range_succ', mul_comm]; rfl
    simp_rw [hpt]
    rw [lintegral_prod_mul (f := f) (g := fun x : ℕ → α => ∏ m ∈ Finset.range n, f (x m))
      hf.aemeasurable hm'.aemeasurable, ih, pow_succ, mul_comm]

lemma ae_good_nu (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(nu r), CMR.Ev t (CMR.Nidx t x) x ∧ ∀ m, 0 ≤ x m := by
  filter_upwards [CMR.ae_exists_Ev hr ht, ae_nonneg_nu (r := r) hr] with x ⟨k, hk⟩ h0
  exact ⟨by rw [CMR.Nidx_eq hk]; exact hk, h0⟩

lemma lintegral_ind_eq (t : ℝ) (k : ℕ) :
    ∫⁻ x, ind t (CMR.psum x k) ∂(nu r) = (nu r) {x | CMR.psum x k ≤ t} := by
  rw [← lintegral_indicator_one (measurableSet_le (CMR.measurable_psum k) measurable_const)]
  refine lintegral_congr fun x => ?_
  simp only [ind, Set.indicator, mem_Iic, mem_setOf_eq]
  rfl

/-- the counting moment: `E q^{N_t} ≤ e^{st} / (1 - q r/(r+s))`. -/
theorem lintegral_pow_Nidx_le (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : 0 ≤ s)
    (q : ENNReal) :
    ∫⁻ x, q ^ (CMR.Nidx t x) ∂(nu r) ≤
      ENNReal.ofReal (Real.exp (s * t)) * (1 - q * ENNReal.ofReal (r / (r + s)))⁻¹ := by
  have hmi : ∀ m, Measurable fun x : ℕ → ℝ => ind t (CMR.psum x m) := fun m =>
    (measurable_ind t).comp (CMR.measurable_psum m)
  have h1 : ∀ᵐ x ∂(nu r), q ^ (CMR.Nidx t x) ≤ ∑' k, q ^ k * ind t (CMR.psum x k) := by
    filter_upwards [ae_good_nu hr ht] with x ⟨hE, h0⟩
    simp_rw [ind_psum_eq ht h0 hE]
    calc q ^ CMR.Nidx t x
        = q ^ (CMR.Nidx t x) * (if CMR.Nidx t x ≤ CMR.Nidx t x then 1 else 0) := by simp
      _ ≤ ∑' k, q ^ k * (if k ≤ CMR.Nidx t x then 1 else 0) :=
          ENNReal.le_tsum (f := fun k => q ^ k * (if k ≤ CMR.Nidx t x then (1 : ENNReal) else 0)) _
  calc ∫⁻ x, q ^ (CMR.Nidx t x) ∂(nu r)
      ≤ ∫⁻ x, ∑' k, q ^ k * ind t (CMR.psum x k) ∂(nu r) := lintegral_mono_ae h1
    _ = ∑' k, q ^ k * ∫⁻ x, ind t (CMR.psum x k) ∂(nu r) := by
        rw [lintegral_tsum (fun k => ((hmi k).const_mul _).aemeasurable)]
        congr 1; funext k; rw [lintegral_const_mul _ (hmi k)]
    _ ≤ ∑' k, q ^ k * (ENNReal.ofReal (Real.exp (s * t)) * ENNReal.ofReal (r / (r + s)) ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        gcongr
        rw [lintegral_ind_eq]; exact meas_psum_le hr hs t k
    _ = ENNReal.ofReal (Real.exp (s * t)) * (1 - q * ENNReal.ofReal (r / (r + s)))⁻¹ := by
        have e : ∀ k : ℕ, q ^ k * (ENNReal.ofReal (Real.exp (s * t)) * ENNReal.ofReal (r / (r + s)) ^ k)
            = ENNReal.ofReal (Real.exp (s * t)) * (q * ENNReal.ofReal (r / (r + s))) ^ k := by
          intro k; rw [mul_pow]; ring
        simp_rw [e]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma measurable_sumN (t : ℝ) :
    Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => ∑ m ∈ Finset.range (CMR.Nidx t p.1), p.2 m := by
  have h : Measurable fun q : ℕ × ((ℕ → ℝ) × (ℕ → ℝ)) => ∑ m ∈ Finset.range q.1, q.2.2 m :=
    measurable_from_prod_countable_right fun n =>
      (show Measurable fun y : (ℕ → ℝ) × (ℕ → ℝ) => ∑ m ∈ Finset.range n, y.2 m from
        Finset.measurable_sum _ fun m _ => (measurable_pi_apply m).comp measurable_snd)
  exact h.comp (((CMR.measurable_Nidx t).comp measurable_fst).prodMk measurable_id)

section Marked
variable {E : Type*} [MeasurableSpace E] {μ : ℝ} [IsProbabilityMeasure (expMeasure μ)]
  (η : Measure E) [IsProbabilityMeasure η]

/-- integrating a function of the arrival and requirement sequences against one stream's law. -/
lemma lintegral_Qs {G : (ℕ → ℝ) → (ℕ → ℝ) → ENNReal}
    (hG : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => G p.1 p.2) :
    ∫⁻ z, G z.1 z.2.1 ∂(CMT.Qs (expMeasure r) (expMeasure μ) η)
      = ∫⁻ x, ∫⁻ y, G x y ∂(nu μ) ∂(nu r) := by
  unfold CMT.Qs
  rw [lintegral_prod _ (show Measurable fun z : CMT.Str E => G z.1 z.2.1 from
    hG.comp (measurable_fst.prodMk measurable_snd.fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_prod _ (show Measurable fun w : (ℕ → ℝ) × (ℕ → E) => G x w.1 from
    hG.comp (measurable_const.prodMk measurable_fst)).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]

/-- the mean work a stream brings in `[0, t]`: `E cW = r t / μ`. -/
theorem lintegral_cW (hr : 0 < r) (hμ : 0 < μ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (CMR.cW t z) ∂(CMT.Qs (expMeasure r) (expMeasure μ) η)
      = ENNReal.ofReal (r * t) * ENNReal.ofReal (1 / μ) := by
  have hG := (measurable_sumN t).ennreal_ofReal
  rw [show (fun z : CMT.Str E => ENNReal.ofReal (CMR.cW t z)) =
      fun z => ENNReal.ofReal (∑ m ∈ Finset.range (CMR.Nidx t z.1), z.2.1 m) from rfl,
    lintegral_Qs η (G := fun x y => ENNReal.ofReal (∑ m ∈ Finset.range (CMR.Nidx t x), y m)) hG]
  have hin : ∀ x : ℕ → ℝ, ∫⁻ y, ENNReal.ofReal (∑ m ∈ Finset.range (CMR.Nidx t x), y m) ∂(nu μ)
      = (CMR.Nidx t x : ENNReal) * ENNReal.ofReal (1 / μ) := by
    intro x
    rw [lintegral_congr_ae (by filter_upwards [ae_nonneg_nu (r := μ) hμ] with y hy using
      ENNReal.ofReal_sum_of_nonneg (fun m _ => hy m)),
      lintegral_finsetSum _ (fun m _ => (show Measurable fun y : ℕ → ℝ => ENNReal.ofReal (y m) from
        ENNReal.measurable_ofReal.comp (measurable_pi_apply m)))]
    simp_rw [lintegral_eval_nu (r := μ) (h := ENNReal.ofReal) ENNReal.measurable_ofReal,
      lintegral_id_expMeasure hμ]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [hin]
  rw [lintegral_mul_const _ (show Measurable fun x : ℕ → ℝ => (CMR.Nidx t x : ENNReal) from
    measurable_from_top.comp (CMR.measurable_Nidx t)), lintegral_Nidx hr ht]

/-- exponential moment of the work a stream brings in `[0, t]`. -/
theorem lintegral_exp_cW_le (hr : 0 < r) (hμ : 0 < μ) {t : ℝ} (ht : 0 ≤ t) {θ : ℝ} (hθ : θ < μ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (θ * CMR.cW t z)) ∂(CMT.Qs (expMeasure r) (expMeasure μ) η)
      ≤ ENNReal.ofReal (Real.exp (s * t)) *
        (1 - ENNReal.ofReal (μ / (μ - θ)) * ENNReal.ofReal (r / (r + s)))⁻¹ := by
  have hG : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ENNReal.ofReal (Real.exp (θ * ∑ m ∈ Finset.range (CMR.Nidx t p.1), p.2 m)) :=
    ((measurable_sumN t).const_mul θ).exp.ennreal_ofReal
  rw [show (fun z : CMT.Str E => ENNReal.ofReal (Real.exp (θ * CMR.cW t z))) =
      fun z => ENNReal.ofReal (Real.exp (θ * ∑ m ∈ Finset.range (CMR.Nidx t z.1), z.2.1 m)) from rfl,
    lintegral_Qs η (G := fun x y =>
      ENNReal.ofReal (Real.exp (θ * ∑ m ∈ Finset.range (CMR.Nidx t x), y m))) hG]
  have hin : ∀ x : ℕ → ℝ,
      ∫⁻ y, ENNReal.ofReal (Real.exp (θ * ∑ m ∈ Finset.range (CMR.Nidx t x), y m)) ∂(nu μ)
        = ENNReal.ofReal (μ / (μ - θ)) ^ (CMR.Nidx t x) := by
    intro x
    have hpt : ∀ y : ℕ → ℝ, ENNReal.ofReal (Real.exp (θ * ∑ m ∈ Finset.range (CMR.Nidx t x), y m))
        = ∏ m ∈ Finset.range (CMR.Nidx t x), ENNReal.ofReal (Real.exp (θ * y m)) := by
      intro y
      rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun m _ => (Real.exp_pos _).le)]
    simp_rw [hpt]
    rw [nu, lintegral_prod_range (expMeasure μ) (f := fun a : ℝ => ENNReal.ofReal (Real.exp (θ * a)))
      ((measurable_id.const_mul θ).exp.ennreal_ofReal),
      lintegral_exp_mul_expMeasure hμ hθ]
  simp_rw [hin]
  exact lintegral_pow_Nidx_le hr ht hs _

end Marked

end Stream

/-! ### P4 part 3: the first window of class `i` -/

lemma ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ k ∈ s, f k) ≤ ∑ k ∈ s, ENNReal.ofReal (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (by gcongr)

section Window
variable {M : ℕ} {E : Type*} [MeasurableSpace E] (lam mu : Fin M → ℝ)
  [∀ k, IsProbabilityMeasure (expMeasure (lam k))] [∀ k, IsProbabilityMeasure (expMeasure (mu k))]
  (η : Measure E) [IsProbabilityMeasure η]

/-- the class laws with exponential requirements. -/
noncomputable abbrev QE : Fin M → Measure (CMT.Str E) :=
  CMT.QQ lam (fun k => expMeasure (mu k)) η

lemma lintegral_eval_pi {k : Fin M} {g : CMT.Str E → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g (y k) ∂(Measure.pi (QE lam mu η)) = ∫⁻ z, g z ∂(QE lam mu η k) :=
  (measurePreserving_eval (QE lam mu η) k).lintegral_comp hg

/-- the factors of the conditional exponential moment. -/
noncomputable def gW (i : Fin M) (T θ : ℝ) (k : Fin M) (z : CMT.Str E) : ENNReal :=
  if k = i then 1 else ENNReal.ofReal (Real.exp (θ * CMR.cW T z))

lemma measurable_gW (i : Fin M) (T θ : ℝ) (k : Fin M) : Measurable (gW (E := E) i T θ k) := by
  unfold gW
  by_cases hk : k = i
  · simp only [if_pos hk]; exact measurable_const
  · simp only [if_neg hk]; exact ((CMR.measurable_cW T).const_mul θ).exp.ennreal_ofReal

lemma exp_sumW_eq (i : Fin M) (T θ : ℝ) (y : Fin M → CMT.Str E) :
    ENNReal.ofReal (Real.exp (θ * CMT.sumW i T y)) = ∏ k, gW i T θ k (y k) := by
  unfold CMT.sumW
  rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le)]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold gW
  by_cases hk : k = i
  · rw [if_pos hk, if_pos hk, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  · rw [if_neg hk, if_neg hk]

/-- conditional exponential moment of the other classes' work in `[0, T]`. -/
theorem lintegral_exp_sumW_le (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    {T : ℝ} (hT : 0 ≤ T) {θ : ℝ} (hθ : ∀ k, θ < mu k) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (θ * CMT.sumW i T y)) ∂(Measure.pi (QE lam mu η))
      ≤ ∏ k, (ENNReal.ofReal (Real.exp (s * T)) *
          (1 - ENNReal.ofReal (mu k / (mu k - θ)) * ENNReal.ofReal (lam k / (lam k + s)))⁻¹) := by
  have hind : iIndepFun (fun k (y : Fin M → CMT.Str E) => gW i T θ k (y k))
      (Measure.pi (QE lam mu η)) :=
    iIndepFun_pi (fun k => (measurable_gW i T θ k).aemeasurable)
  simp_rw [exp_sumW_eq]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun k => (measurable_gW i T θ k).comp (measurable_pi_apply k))]
  refine Finset.prod_le_prod' fun k _ => ?_
  rw [lintegral_eval_pi lam mu η (measurable_gW i T θ k)]
  by_cases hk : k = i
  · have e : gW (E := E) i T θ k = fun _ => 1 := by funext z; unfold gW; rw [if_pos hk]
    rw [e, lintegral_const, measure_univ, mul_one]
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (s * T)) := by
      rw [ENNReal.one_le_ofReal]; exact Real.one_le_exp (by positivity)
    have h2 : (1 : ENNReal) ≤ (1 - ENNReal.ofReal (mu k / (mu k - θ)) *
        ENNReal.ofReal (lam k / (lam k + s)))⁻¹ := ENNReal.one_le_inv.2 tsub_le_self
    calc (1 : ENNReal) = 1 * 1 := (mul_one 1).symm
      _ ≤ _ := mul_le_mul' h1 h2
  · have e : gW (E := E) i T θ k = fun z => ENNReal.ofReal (Real.exp (θ * CMR.cW T z)) := by
      funext z; unfold gW; rw [if_neg hk]
    rw [e]
    exact lintegral_exp_cW_le (r := lam k) (μ := mu k) η (hlam k) (hmu k) hT (hθ k) hs

/-- conditional mean of the other classes' work in `[0, T]`. -/
theorem lintegral_sumW_le (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ y, ENNReal.ofReal (CMT.sumW i T y) ∂(Measure.pi (QE lam mu η))
      ≤ ∑ k, if k = i then 0 else ENNReal.ofReal (lam k * T) * ENNReal.ofReal (1 / mu k) := by
  classical
  have hm : ∀ k, Measurable fun z : CMT.Str E =>
      ENNReal.ofReal (if k = i then 0 else CMR.cW T z) := by
    intro k
    by_cases hk : k = i
    · simp only [if_pos hk]; exact measurable_const
    · simp only [if_neg hk]; exact (CMR.measurable_cW T).ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (CMT.sumW i T y) ∂(Measure.pi (QE lam mu η))
      ≤ ∫⁻ y, ∑ k, ENNReal.ofReal (if k = i then 0 else CMR.cW T (y k))
          ∂(Measure.pi (QE lam mu η)) := lintegral_mono fun y => ofReal_sum_le' _ _
    _ = ∑ k, ∫⁻ y, ENNReal.ofReal (if k = i then 0 else CMR.cW T (y k))
          ∂(Measure.pi (QE lam mu η)) :=
        lintegral_finsetSum _ fun k _ => (hm k).comp (measurable_pi_apply k)
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_eval_pi lam mu η (hm k)]
        by_cases hk : k = i
        · simp [hk]
        · simp only [if_neg hk]
          exact lintegral_cW (r := lam k) (μ := mu k) η (hlam k) (hmu k) hT

/-- integrating against the law of class `i`'s first window `(r, A, τ)`. -/
theorem lintegral_win (i : Fin M) {g : ℝ × ℝ × ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ w, g w ∂((Measure.pi (QE lam mu η)).map (CMT.WinS i)) =
      ∫⁻ τ, ∫⁻ re : ℝ × E, ∫⁻ y, g (re.1, CMT.sumW i τ y, τ) ∂(Measure.pi (QE lam mu η))
        ∂((expMeasure (mu i)).prod η) ∂(expMeasure (lam i)) := by
  have hF : Measurable fun p : (ℝ × ℝ × E) × (Fin M → CMT.Str E) =>
      (p.1.2.1, CMT.sumW i p.1.1 p.2, p.1.1) := by
    have h1 : Measurable fun p : (ℝ × ℝ × E) × (Fin M → CMT.Str E) => (p.1.1, p.2) :=
      measurable_fst.fst.prodMk measurable_snd
    have h2 := (CMT.measurable_sumW₂ (E := E) i).comp h1
    exact measurable_fst.snd.fst.prodMk (h2.prodMk measurable_fst.fst)
  have hgF : Measurable fun p : (ℝ × ℝ × E) × (Fin M → CMT.Str E) =>
      g (p.1.2.1, CMT.sumW i p.1.1 p.2, p.1.1) := hg.comp hF
  rw [CMT.law_WinS, lintegral_map hg hF, lintegral_prod _ hgF.aemeasurable]
  unfold CMT.Hs
  have hin : Measurable fun h : ℝ × ℝ × E => ∫⁻ y, g (h.2.1, CMT.sumW i h.1 y, h.1)
      ∂(Measure.pi (QE lam mu η)) := hgF.lintegral_prod_right'
  rw [lintegral_prod _ hin.aemeasurable]

/-! ### P4 part 3b: exponential moments of the window, `E Y < 0`, and a Chernoff base `< 1` -/

/-- the law of class `i`'s first window `(r, A, τ)`. -/
noncomputable abbrev zeta (i : Fin M) : Measure (ℝ × ℝ × ℝ) :=
  (Measure.pi (QE lam mu η)).map (CMT.WinS i)

lemma isProb_zeta (i : Fin M) : IsProbabilityMeasure (zeta lam mu η i) :=
  Measure.isProbabilityMeasure_map (CMT.measurable_WinS i).aemeasurable

lemma lintegral_zeta_tau (i : Fin M) {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ w, f w.2.2 ∂(zeta lam mu η i) = ∫⁻ τ, f τ ∂(expMeasure (lam i)) := by
  refine (lintegral_win lam mu η i (g := fun w => f w.2.2) (hf.comp measurable_snd.snd)).trans ?_
  simp only [lintegral_const, measure_univ, mul_one]

/-- master bound: the joint exponential moment of `(r + A, τ)`. -/
theorem lintegral_exp_win_le (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    {θ c s : ℝ} (hθ : ∀ k, θ < mu k) (hs : 0 ≤ s) (hc : M * s + c < lam i) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1) + c * w.2.2)) ∂(zeta lam mu η i)
      ≤ ENNReal.ofReal (mu i / (mu i - θ)) * (ENNReal.ofReal (lam i / (lam i - (M * s + c))) *
        ∏ k, (1 - ENNReal.ofReal (mu k / (mu k - θ)) * ENNReal.ofReal (lam k / (lam k + s)))⁻¹) := by
  set P := ∏ k, (1 - ENNReal.ofReal (mu k / (mu k - θ)) *
    ENNReal.ofReal (lam k / (lam k + s)))⁻¹ with hP
  have hmeas : Measurable fun w : ℝ × ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1) + c * w.2.2)) := by fun_prop
  rw [lintegral_win lam mu η i hmeas]
  have h1 : ∀ τ : ℝ, 0 ≤ τ → ∀ re : ℝ × E,
      ∫⁻ y, ENNReal.ofReal (Real.exp (θ * (re.1 + CMT.sumW i τ y) + c * τ))
        ∂(Measure.pi (QE lam mu η))
      ≤ ENNReal.ofReal (Real.exp (θ * re.1)) *
          (ENNReal.ofReal (Real.exp ((M * s + c) * τ)) * P) := by
    intro τ hτ re
    have hy : Measurable fun y : Fin M → CMT.Str E =>
        ENNReal.ofReal (Real.exp (θ * CMT.sumW i τ y)) :=
      (((CMT.measurable_sumW₂ (E := E) i).comp
        (measurable_const.prodMk measurable_id)).const_mul θ).exp.ennreal_ofReal
    have he : ∀ y : Fin M → CMT.Str E,
        ENNReal.ofReal (Real.exp (θ * (re.1 + CMT.sumW i τ y) + c * τ)) =
          ENNReal.ofReal (Real.exp (θ * re.1 + c * τ)) *
            ENNReal.ofReal (Real.exp (θ * CMT.sumW i τ y)) := by
      intro y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    simp_rw [he]
    rw [lintegral_const_mul _ hy]
    have hb := lintegral_exp_sumW_le lam mu η hlam hmu i hτ hθ hs
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
    calc ENNReal.ofReal (Real.exp (θ * re.1 + c * τ)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (θ * CMT.sumW i τ y)) ∂(Measure.pi (QE lam mu η))
        ≤ ENNReal.ofReal (Real.exp (θ * re.1 + c * τ)) *
            (ENNReal.ofReal (Real.exp (s * τ)) ^ M * P) := by gcongr
      _ = ENNReal.ofReal (Real.exp (θ * re.1) * Real.exp ((M * s + c) * τ)) * P := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add]
        congr 3; ring
      _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  calc ∫⁻ τ, ∫⁻ re : ℝ × E, ∫⁻ y, ENNReal.ofReal (Real.exp (θ * (re.1 + CMT.sumW i τ y) + c * τ))
          ∂(Measure.pi (QE lam mu η)) ∂((expMeasure (mu i)).prod η) ∂(expMeasure (lam i))
      ≤ ∫⁻ τ, ∫⁻ re : ℝ × E, ENNReal.ofReal (Real.exp (θ * re.1)) *
          (ENNReal.ofReal (Real.exp ((M * s + c) * τ)) * P)
            ∂((expMeasure (mu i)).prod η) ∂(expMeasure (lam i)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [CMT.ae_pos_exp (lam i)] with τ hτ
        exact lintegral_mono fun re => h1 τ hτ.le re
    _ = ∫⁻ τ, ENNReal.ofReal (mu i / (mu i - θ)) *
          (ENNReal.ofReal (Real.exp ((M * s + c) * τ)) * P) ∂(expMeasure (lam i)) := by
        refine lintegral_congr fun τ => ?_
        rw [lintegral_mul_const _ (by fun_prop)]
        congr 1
        rw [lintegral_prod _ (by fun_prop : Measurable fun re : ℝ × E =>
          ENNReal.ofReal (Real.exp (θ * re.1))).aemeasurable]
        simp only [lintegral_const, measure_univ, mul_one]
        exact lintegral_exp_mul_expMeasure (hmu i) (hθ i)
    _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_mul_const _ (by fun_prop),
          lintegral_exp_mul_expMeasure (hlam i) hc]

lemma prodC_lt_top (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) {θ s : ℝ} (hs : 0 < s)
    (hθ : ∀ k, θ * (lam k + s) < mu k * s) :
    ∏ k, (1 - ENNReal.ofReal (mu k / (mu k - θ)) * ENNReal.ofReal (lam k / (lam k + s)))⁻¹ < ⊤ := by
  refine ENNReal.prod_lt_top fun k _ => ?_
  have hl := hlam k
  have hm := hmu k
  have h := hθ k
  have hmt : 0 < mu k - θ := by nlinarith
  rw [ENNReal.inv_lt_top, tsub_pos_iff_lt, ← ENNReal.ofReal_mul (div_nonneg hm.le hmt.le),
    ENNReal.ofReal_lt_one, div_mul_div_comm, div_lt_one (by positivity)]
  nlinarith

lemma integrable_exp_win (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    {s θ c : ℝ} (hs : 0 < s) (hθ : ∀ k, θ * (lam k + s) < mu k * s) (hc : M * s + c < lam i) :
    Integrable (fun w : ℝ × ℝ × ℝ => Real.exp (θ * (w.1 + w.2.1) + c * w.2.2))
      (zeta lam mu η i) := by
  have hθ' : ∀ k, θ < mu k := fun k => by
    have := hθ k; have := hlam k; have := hmu k; nlinarith
  refine ⟨(by fun_prop : Measurable fun w : ℝ × ℝ × ℝ =>
    Real.exp (θ * (w.1 + w.2.1) + c * w.2.2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => (Real.exp_pos _).le)]
  refine (lintegral_exp_win_le lam mu η hlam hmu i hθ' hs.le hc).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (prodC_lt_top lam mu hlam hmu hs hθ))

/-- the mean of `r + A` under the window law. -/
theorem lintegral_Z_le (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M) :
    ∫⁻ w, ENNReal.ofReal (w.1 + w.2.1) ∂(zeta lam mu η i) ≤
      ENNReal.ofReal (1 / mu i) +
        ENNReal.ofReal (∑ k ∈ Finset.univ.erase i, lam k / mu k) * ENNReal.ofReal (1 / lam i) := by
  set q := ∑ k ∈ Finset.univ.erase i, lam k / mu k with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun k _ => by
    have := hlam k; have := hmu k; positivity
  have hA : ∀ τ : ℝ, 0 ≤ τ → ∫⁻ y, ENNReal.ofReal (CMT.sumW i τ y) ∂(Measure.pi (QE lam mu η))
      ≤ ENNReal.ofReal q * ENNReal.ofReal τ := by
    intro τ hτ
    refine (lintegral_sumW_le lam mu η hlam hmu i hτ).trans (le_of_eq ?_)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add,
      ← ENNReal.ofReal_mul hq0, hq, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun k _ => mul_nonneg (by have := hlam k; have := hmu k; positivity) hτ)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (Finset.ne_of_mem_erase hk),
      ← ENNReal.ofReal_mul (mul_nonneg (hlam k).le hτ)]
    congr 1; ring
  rw [lintegral_win lam mu η i (by fun_prop)]
  calc ∫⁻ τ, ∫⁻ re : ℝ × E, ∫⁻ y, ENNReal.ofReal (re.1 + CMT.sumW i τ y)
          ∂(Measure.pi (QE lam mu η)) ∂((expMeasure (mu i)).prod η) ∂(expMeasure (lam i))
      ≤ ∫⁻ τ, ∫⁻ re : ℝ × E, (ENNReal.ofReal re.1 + ENNReal.ofReal q * ENNReal.ofReal τ)
            ∂((expMeasure (mu i)).prod η) ∂(expMeasure (lam i)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [CMT.ae_pos_exp (lam i)] with τ hτ
        refine lintegral_mono fun re => ?_
        calc ∫⁻ y, ENNReal.ofReal (re.1 + CMT.sumW i τ y) ∂(Measure.pi (QE lam mu η))
            ≤ ∫⁻ y, (ENNReal.ofReal re.1 + ENNReal.ofReal (CMT.sumW i τ y))
                ∂(Measure.pi (QE lam mu η)) := lintegral_mono fun y => ENNReal.ofReal_add_le
          _ = ENNReal.ofReal re.1 + ∫⁻ y, ENNReal.ofReal (CMT.sumW i τ y)
                ∂(Measure.pi (QE lam mu η)) := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ _ := by gcongr; exact hA τ hτ.le
    _ = ∫⁻ τ, (ENNReal.ofReal (1 / mu i) + ENNReal.ofReal q * ENNReal.ofReal τ)
          ∂(expMeasure (lam i)) := by
        refine lintegral_congr fun τ => ?_
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_prod _ (by fun_prop : Measurable fun re : ℝ × E =>
            ENNReal.ofReal re.1).aemeasurable]
        simp only [lintegral_const, measure_univ, mul_one]
        rw [lintegral_id_expMeasure (hmu i)]
    _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ ENNReal.measurable_ofReal, lintegral_id_expMeasure (hlam i)]

end Window

open Filter Topology in
/-- a negative mean forces the moment generating function below `1` just right of `0`. -/
theorem exists_mgf_lt_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hint : ∀ t ∈ Ioo (-a) b, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hX : ∫ ω, X ω ∂μ < 0) :
    ∃ θ ∈ Ioo 0 b, mgf X μ θ < 1 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset (Ioo_mem_nhds (by linarith) hb) fun t ht => hint t ht)
  have hd := hasDerivAt_mgf h0
  simp only [zero_mul, Real.exp_zero, mul_one] at hd
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (mgf X μ) 0 t < 0 :=
    (hs.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')).eventually
      (eventually_lt_nhds hX)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 b := Ioo_mem_nhdsGT hb
  obtain ⟨θ, h1, h2⟩ := (hev.and hev2).exists
  refine ⟨θ, h2, ?_⟩
  rw [slope_def_field, mgf_zero, sub_zero] at h1
  by_contra hc
  exact absurd h1 (not_lt.2 (div_nonneg (by linarith [not_lt.1 hc]) h2.1.le))

section Window2
variable {M : ℕ} {E : Type*} [MeasurableSpace E] (lam mu : Fin M → ℝ)
  [∀ k, IsProbabilityMeasure (expMeasure (lam k))] [∀ k, IsProbabilityMeasure (expMeasure (mu k))]
  (η : Measure E) [IsProbabilityMeasure η]

lemma zero_mem_interior_of {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (h : ∀ t ∈ Ioo a b, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet X μ) :=
  mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Ioo_mem_nhds ha hb) fun t ht => h t ht)

/-- P4 part 3b: a Chernoff exponent for the window: `E e^{θ Z} < ∞` and `E e^{θ Y} < 1`,
where `Z = r + A` and `Y = r + A - τ`, under the load condition `∑ λ_k / μ_k < 1`. -/
theorem exists_theta_win (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    (hρ : ∑ k, lam k / mu k < 1) :
    ∃ θ > 0, ∫⁻ w, ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1))) ∂(zeta lam mu η i) < ⊤ ∧
      ∫⁻ w, ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1 - w.2.2))) ∂(zeta lam mu η i) < 1 := by
  haveI := isProb_zeta lam mu η i
  have hli := hlam i
  have hmi := hmu i
  set s : ℝ := lam i / (2 * (M + 1)) with hs_def
  have hs : 0 < s := by positivity
  have hMs : (M : ℝ) * s < lam i / 2 := by
    have : lam i / 2 - M * s = s := by rw [hs_def]; field_simp; ring
    linarith
  set b : ℝ := Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ fun k => mu k * s / (lam k + s) with hb_def
  have hb : 0 < b := (Finset.lt_inf'_iff _).2 fun k _ => by
    have := hlam k; have := hmu k; positivity
  have hcond : ∀ θ, θ < b → ∀ k, θ * (lam k + s) < mu k * s := fun θ hθ k => by
    have h := lt_of_lt_of_le hθ (Finset.inf'_le _ (Finset.mem_univ k))
    have := hlam k
    rwa [lt_div_iff₀ (by positivity)] at h
  have hintY : ∀ t ∈ Ioo (-(lam i / 2)) b,
      Integrable (fun w : ℝ × ℝ × ℝ => Real.exp (t * (w.1 + w.2.1 - w.2.2))) (zeta lam mu η i) := by
    intro t ht
    refine (integrable_exp_win lam mu η hlam hmu i hs (hcond t ht.2) (c := -t)
      (by linarith [ht.1])).congr (ae_of_all _ fun w => ?_)
    simp only
    congr 1; ring
  have hintZ : ∀ t ∈ Ioo (-1) b,
      Integrable (fun w : ℝ × ℝ × ℝ => Real.exp (t * (w.1 + w.2.1))) (zeta lam mu η i) := by
    intro t ht
    refine (integrable_exp_win lam mu η hlam hmu i hs (hcond t ht.2) (c := 0)
      (by linarith)).congr (ae_of_all _ fun w => ?_)
    simp only [zero_mul, add_zero]
  have hintT : ∀ t ∈ Ioo (-1) (lam i / 2),
      Integrable (fun w : ℝ × ℝ × ℝ => Real.exp (t * w.2.2)) (zeta lam mu η i) := by
    intro t ht
    refine (integrable_exp_win lam mu η hlam hmu i hs (hcond 0 hb) (c := t)
      (by linarith [ht.2])).congr (ae_of_all _ fun w => ?_)
    simp only [zero_mul, zero_add]
  have hZi := ProbabilityTheory.integrable_of_mem_interior_integrableExpSet
    (zero_mem_interior_of (by norm_num) hb hintZ)
  have hTi := ProbabilityTheory.integrable_of_mem_interior_integrableExpSet
    (zero_mem_interior_of (by norm_num) (by linarith) hintT)
  -- the means
  set q := ∑ k ∈ Finset.univ.erase i, lam k / mu k with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun k _ => by
    have := hlam k; have := hmu k; positivity
  have hρq : lam i / mu i + q = ∑ k, lam k / mu k := by
    rw [hq]; exact Finset.add_sum_erase _ (fun k => lam k / mu k) (Finset.mem_univ i)
  have hEZ : ∫ w, (w.1 + w.2.1) ∂(zeta lam mu η i) ≤ 1 / mu i + q * (1 / lam i) := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hZi]
    refine (sub_le_self _ ENNReal.toReal_nonneg).trans ?_
    have hL := lintegral_Z_le lam mu η hlam hmu i
    refine (ENNReal.toReal_mono (by simp [ENNReal.add_eq_top, ENNReal.mul_eq_top]) hL).trans
      (le_of_eq ?_)
    rw [ENNReal.toReal_add (by simp) (by simp [ENNReal.mul_eq_top]), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hq0,
      ENNReal.toReal_ofReal (by positivity)]
  have hET : ∫ w, w.2.2 ∂(zeta lam mu η i) = 1 / lam i := by
    have h1 : ∫⁻ w, ENNReal.ofReal w.2.2 ∂(zeta lam mu η i) = ENNReal.ofReal (1 / lam i) :=
      (lintegral_zeta_tau lam mu η i ENNReal.measurable_ofReal).trans (lintegral_id_expMeasure hli)
    have h2 : ∫⁻ w, ENNReal.ofReal (-w.2.2) ∂(zeta lam mu η i) = 0 := by
      refine (lintegral_zeta_tau lam mu η i (f := fun x => ENNReal.ofReal (-x))
        (by fun_prop)).trans ?_
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [CMT.ae_pos_exp (lam i)] with τ hτ
      exact ENNReal.ofReal_of_nonpos (by linarith)
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hTi, h1, h2,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_zero, sub_zero]
  have hEY : ∫ w, (w.1 + w.2.1 - w.2.2) ∂(zeta lam mu η i) < 0 := by
    rw [integral_sub hZi hTi, hET]
    have : 1 / mu i + q * (1 / lam i) - 1 / lam i = (lam i / mu i + q - 1) / lam i := by
      field_simp
    have hneg : (lam i / mu i + q - 1) / lam i < 0 := div_neg_of_neg_of_pos (by linarith) hli
    linarith
  obtain ⟨θ, ⟨hθ0, hθb⟩, hmgf⟩ := exists_mgf_lt_one (μ := zeta lam mu η i)
    (X := fun w : ℝ × ℝ × ℝ => w.1 + w.2.1 - w.2.2) (a := lam i / 2) (b := b) (by positivity) hb
    hintY hEY
  refine ⟨θ, hθ0, ?_, ?_⟩
  · exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => (Real.exp_pos _).le)).1
      (hintZ θ ⟨by linarith, hθb⟩).hasFiniteIntegral
  · refine lt_of_eq_of_lt (Eq.symm ?_) (ENNReal.ofReal_lt_one.2 hmgf)
    exact ofReal_integral_eq_lintegral_ofReal (hintY θ ⟨by linarith, hθb⟩)
      (ae_of_all _ fun w => (Real.exp_pos _).le)

end Window2

/-! ### P4 part 4: the i.i.d. Chernoff bound for the busy-period majorant -/

section Chernoff
open Finset

/-- partial sums of `Y = r + A - τ` over the `L` windows after window `k`. -/
noncomputable def Sy (ws : ℕ → ℝ × ℝ × ℝ) (k L : ℕ) : ℝ :=
  ∑ l ∈ range L, ((ws (k + 1 + l)).1 + (ws (k + 1 + l)).2.1 - (ws (k + 1 + l)).2.2)

/-- the Lindley majorant after window `n`: `max_{k ≤ n} (Z_k + Y_{k+1} + ... + Y_n)`. -/
noncomputable def Xb (ws : ℕ → ℝ × ℝ × ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' ⟨0, mem_range.2 n.succ_pos⟩ fun k => (ws k).1 + (ws k).2.1 + Sy ws k (n - k)

/-- the busy-period majorant after window `n`. -/
noncomputable def Bnd (ws : ℕ → ℝ × ℝ × ℝ) (n : ℕ) : ENNReal :=
  ∑' K, ENNReal.ofReal (ws (n + K + 1)).2.2 * (if 0 ≤ Xb ws n + Sy ws n K then 1 else 0)

noncomputable def eZ (θ : ℝ) (w : ℝ × ℝ × ℝ) : ENNReal := ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1)))
noncomputable def eY (θ : ℝ) (w : ℝ × ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (θ * (w.1 + w.2.1 - w.2.2)))
noncomputable def oT (w : ℝ × ℝ × ℝ) : ENNReal := ENNReal.ofReal w.2.2

lemma measurable_eZ (θ : ℝ) : Measurable (eZ θ) := by unfold eZ; fun_prop
lemma measurable_eY (θ : ℝ) : Measurable (eY θ) := by unfold eY; fun_prop
lemma measurable_oT : Measurable oT := by unfold oT; fun_prop

noncomputable def pat (k L : ℕ) (A B C : ℕ → ENNReal) (j : ℕ) : ENNReal :=
  if j < k then 1 else if j = k then A j else if j ≤ k + L then B j else C j

lemma prod_pat (k L : ℕ) (A B C : ℕ → ENNReal) :
    ∏ j ∈ range (k + L + 2), pat k L A B C j
      = A k * (∏ x ∈ range L, B (k + 1 + x)) * C (k + L + 1) := by
  rw [show k + L + 2 = k + (L + 1) + 1 by omega, prod_range_succ, prod_range_add, prod_range_succ']
  have h1 : ∏ x ∈ range k, pat k L A B C x = 1 :=
    prod_eq_one fun x hx => by unfold pat; rw [if_pos (mem_range.1 hx)]
  have e0 : pat k L A B C (k + 0) = A k := by
    unfold pat; split_ifs <;> first | (exfalso; omega) | rfl
  have eL : pat k L A B C (k + (L + 1)) = C (k + L + 1) := by
    unfold pat; split_ifs <;> first | (exfalso; omega) | rfl
  have h2 : ∀ x ∈ range L, pat k L A B C (k + (x + 1)) = B (k + 1 + x) := by
    intro x hx
    have := mem_range.1 hx
    unfold pat; split_ifs <;> first | (exfalso; omega) | (congr 1; omega)
  rw [h1, e0, eL, prod_congr rfl h2]
  ring

lemma lintegral_prod_coord {α : Type*} [MeasurableSpace α] (ν0 : Measure α)
    [IsProbabilityMeasure ν0] (f : ℕ → α → ENNReal) (hf : ∀ j, Measurable (f j)) (S : Finset ℕ) :
    ∫⁻ x, ∏ j ∈ S, f j (x j) ∂(Measure.infinitePi fun _ : ℕ => ν0) = ∏ j ∈ S, ∫⁻ a, f j a ∂ν0 := by
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun S (fun j (x : ℕ → α) => f j (x j))
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν0) hf)
      (fun j => (hf j).comp (measurable_pi_apply j))).trans ?_
  refine prod_congr rfl fun j _ => ?_
  rw [← lintegral_map (hf j) (measurable_pi_apply j), Measure.infinitePi_map_eval]

noncomputable def Ff (θ : ℝ) (k L j : ℕ) (w : ℝ × ℝ × ℝ) : ENNReal :=
  pat k L (fun _ => eZ θ w) (fun _ => eY θ w) (fun _ => oT w) j

lemma measurable_Ff (θ : ℝ) (k L j : ℕ) : Measurable (Ff θ k L j) := by
  unfold Ff pat
  split_ifs
  · exact measurable_const
  · exact measurable_eZ θ
  · exact measurable_eY θ
  · exact measurable_oT

variable {ζ : Measure (ℝ × ℝ × ℝ)} [IsProbabilityMeasure ζ]

lemma lintegral_Ff (θ : ℝ) (k L j : ℕ) :
    ∫⁻ w, Ff θ k L j w ∂ζ = pat k L (fun _ => ∫⁻ w, eZ θ w ∂ζ) (fun _ => ∫⁻ w, eY θ w ∂ζ)
      (fun _ => ∫⁻ w, oT w ∂ζ) j := by
  unfold Ff pat
  split_ifs <;> simp

lemma measurable_term (θ : ℝ) (k L : ℕ) : Measurable fun ws : ℕ → ℝ × ℝ × ℝ =>
    eZ θ (ws k) * (∏ x ∈ range L, eY θ (ws (k + 1 + x))) * oT (ws (k + L + 1)) :=
  (((measurable_eZ θ).comp (measurable_pi_apply k)).mul
    (Finset.measurable_prod _ fun x _ => (measurable_eY θ).comp (measurable_pi_apply _))).mul
    (measurable_oT.comp (measurable_pi_apply _))

theorem lintegral_term (θ : ℝ) (k L : ℕ) :
    ∫⁻ ws, eZ θ (ws k) * (∏ x ∈ range L, eY θ (ws (k + 1 + x))) * oT (ws (k + L + 1))
        ∂(Measure.infinitePi fun _ : ℕ => ζ)
      = (∫⁻ w, eZ θ w ∂ζ) * (∫⁻ w, eY θ w ∂ζ) ^ L * ∫⁻ w, oT w ∂ζ := by
  calc ∫⁻ ws, eZ θ (ws k) * (∏ x ∈ range L, eY θ (ws (k + 1 + x))) * oT (ws (k + L + 1))
        ∂(Measure.infinitePi fun _ : ℕ => ζ)
      = ∫⁻ ws, ∏ j ∈ range (k + L + 2), Ff θ k L j (ws j) ∂(Measure.infinitePi fun _ : ℕ => ζ) := by
        refine lintegral_congr fun ws => ?_
        rw [show ∏ j ∈ range (k + L + 2), Ff θ k L j (ws j) =
            ∏ j ∈ range (k + L + 2), pat k L (fun j => eZ θ (ws j)) (fun j => eY θ (ws j))
              (fun j => oT (ws j)) j from prod_congr rfl fun j _ => rfl, prod_pat]
    _ = ∏ j ∈ range (k + L + 2), ∫⁻ w, Ff θ k L j w ∂ζ :=
        lintegral_prod_coord ζ _ (fun j => measurable_Ff θ k L j) _
    _ = _ := by
        simp_rw [lintegral_Ff]
        rw [prod_pat, prod_const, card_range]

lemma Sy_add (ws : ℕ → ℝ × ℝ × ℝ) {k n : ℕ} (hk : k ≤ n) (K : ℕ) :
    Sy ws k (n - k) + Sy ws n K = Sy ws k (n - k + K) := by
  unfold Sy
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [show k + 1 + (n - k + l) = n + 1 + l by omega]

lemma ind_le_exp {θ x : ℝ} (hθ : 0 < θ) :
    (if 0 ≤ x then (1 : ENNReal) else 0) ≤ ENNReal.ofReal (Real.exp (θ * x)) := by
  split_ifs with h
  · rw [ENNReal.one_le_ofReal]; exact Real.one_le_exp (mul_nonneg hθ.le h)
  · exact zero_le

lemma Bnd_le (ws : ℕ → ℝ × ℝ × ℝ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    Bnd ws n ≤ ∑' K, ∑ k ∈ range (n + 1), eZ θ (ws k) *
      (∏ x ∈ range (n - k + K), eY θ (ws (k + 1 + x))) * oT (ws (k + (n - k + K) + 1)) := by
  unfold Bnd
  refine ENNReal.tsum_le_tsum fun K => ?_
  obtain ⟨k0, hk0, he⟩ : ∃ k ∈ range (n + 1), Xb ws n = (ws k).1 + (ws k).2.1 + Sy ws k (n - k) :=
    Finset.exists_mem_eq_sup' ⟨0, mem_range.2 n.succ_pos⟩ _
  have hk0n : k0 ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk0)
  have hind : (if 0 ≤ Xb ws n + Sy ws n K then (1 : ENNReal) else 0) ≤
      ENNReal.ofReal (Real.exp (θ * ((ws k0).1 + (ws k0).2.1 + Sy ws k0 (n - k0 + K)))) := by
    have : Xb ws n + Sy ws n K = (ws k0).1 + (ws k0).2.1 + Sy ws k0 (n - k0 + K) := by
      rw [he, add_assoc, Sy_add ws hk0n K]
    rw [this]; exact ind_le_exp hθ
  have hterm : ENNReal.ofReal (ws (n + K + 1)).2.2 *
      ENNReal.ofReal (Real.exp (θ * ((ws k0).1 + (ws k0).2.1 + Sy ws k0 (n - k0 + K)))) =
      eZ θ (ws k0) * (∏ x ∈ range (n - k0 + K), eY θ (ws (k0 + 1 + x))) *
        oT (ws (k0 + (n - k0 + K) + 1)) := by
    rw [show k0 + (n - k0 + K) + 1 = n + K + 1 by omega]
    unfold eZ eY oT Sy
    rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)]
    ring
  calc ENNReal.ofReal (ws (n + K + 1)).2.2 * (if 0 ≤ Xb ws n + Sy ws n K then 1 else 0)
      ≤ ENNReal.ofReal (ws (n + K + 1)).2.2 *
          ENNReal.ofReal (Real.exp (θ * ((ws k0).1 + (ws k0).2.1 + Sy ws k0 (n - k0 + K)))) :=
        mul_le_mul' le_rfl hind
    _ = _ := hterm
    _ ≤ _ := single_le_sum (f := fun k => eZ θ (ws k) *
          (∏ x ∈ range (n - k + K), eY θ (ws (k + 1 + x))) * oT (ws (k + (n - k + K) + 1)))
        (fun _ _ => zero_le) hk0

/-- **P4 part 4.** `E Bnd_n ≤ E e^{θZ} · E τ · (1 - E e^{θY})⁻²`, uniformly in `n`. -/
theorem lintegral_Bnd_le {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∫⁻ ws, Bnd ws n ∂(Measure.infinitePi fun _ : ℕ => ζ) ≤
      (∫⁻ w, eZ θ w ∂ζ) * (∫⁻ w, oT w ∂ζ) *
        ((1 - ∫⁻ w, eY θ w ∂ζ)⁻¹ * (1 - ∫⁻ w, eY θ w ∂ζ)⁻¹) := by
  set CZ := ∫⁻ w, eZ θ w ∂ζ
  set a := ∫⁻ w, eY θ w ∂ζ
  set ET := ∫⁻ w, oT w ∂ζ
  have hrefl : ∑ k ∈ range (n + 1), a ^ (n - k) = ∑ k ∈ range (n + 1), a ^ k := by
    rw [show ∑ k ∈ range (n + 1), a ^ (n - k) = ∑ k ∈ range (n + 1), (fun j => a ^ j) (n + 1 - 1 - k)
      from sum_congr rfl fun k _ => by simp, sum_range_reflect (fun j => a ^ j)]
  calc ∫⁻ ws, Bnd ws n ∂(Measure.infinitePi fun _ : ℕ => ζ)
      ≤ ∫⁻ ws, ∑' K, ∑ k ∈ range (n + 1), eZ θ (ws k) *
          (∏ x ∈ range (n - k + K), eY θ (ws (k + 1 + x))) * oT (ws (k + (n - k + K) + 1))
          ∂(Measure.infinitePi fun _ : ℕ => ζ) := lintegral_mono fun ws => Bnd_le ws n hθ
    _ = ∑' K, ∑ k ∈ range (n + 1), CZ * a ^ (n - k + K) * ET := by
        rw [lintegral_tsum (fun K => (Finset.measurable_sum _ fun k _ =>
          measurable_term θ k (n - k + K)).aemeasurable)]
        refine tsum_congr fun K => ?_
        rw [lintegral_finsetSum _ (fun k _ => measurable_term θ k (n - k + K))]
        exact sum_congr rfl fun k _ => lintegral_term θ k (n - k + K)
    _ = ∑' K, CZ * ET * (a ^ K * ∑ k ∈ range (n + 1), a ^ (n - k)) := by
        refine tsum_congr fun K => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [pow_add]; ring
    _ ≤ ∑' K, CZ * ET * (a ^ K * ∑' j, a ^ j) := by
        refine ENNReal.tsum_le_tsum fun K => mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        rw [hrefl]; exact ENNReal.sum_le_tsum _
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

end Chernoff

section Window3
variable {M : ℕ} {E : Type*} [MeasurableSpace E] (lam mu : Fin M → ℝ)
  [∀ k, IsProbabilityMeasure (expMeasure (lam k))] [∀ k, IsProbabilityMeasure (expMeasure (mu k))]
  (η : Measure E) [IsProbabilityMeasure η]

/-- **P4.** Under the load condition the busy-period majorants have uniformly bounded means on the
i.i.d. window space of class `i`. -/
theorem Bnd_bounded (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (i : Fin M)
    (hρ : ∑ k, lam k / mu k < 1) :
    haveI := isProb_zeta lam mu η i
    ∃ C < ⊤, ∀ n, ∫⁻ ws, Bnd ws n ∂(Measure.infinitePi fun _ : ℕ => zeta lam mu η i) ≤ C := by
  haveI := isProb_zeta lam mu η i
  obtain ⟨θ, hθ, hZ, hY⟩ := exists_theta_win lam mu η hlam hmu i hρ
  refine ⟨_, ?_, fun n => lintegral_Bnd_le hθ n⟩
  have hT : ∫⁻ w, oT w ∂(zeta lam mu η i) = ENNReal.ofReal (1 / lam i) :=
    (lintegral_zeta_tau lam mu η i ENNReal.measurable_ofReal).trans (lintegral_id_expMeasure (hlam i))
  have hinv : (1 - ∫⁻ w, eY θ w ∂(zeta lam mu η i))⁻¹ < ⊤ :=
    ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hY)
  rw [hT]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hZ ENNReal.ofReal_lt_top)
    (ENNReal.mul_lt_top hinv hinv)

end Window3

end CMU


/-! P3 (Mathlib part) for e14b429d: deterministic workload facts used by the pathwise coupling
and the busy-period bound. Needs D1 (CMQ) and P2a (CMR). -/

set_option autoImplicit false

open MeasureTheory Set Finset

namespace CMQ
variable {ι : Type*}

/-- Q1: a negative drift from every arrival up to `x` forces the system to empty in `(x, T]`. -/
theorem exists_Wl_zero_drift (F : Finset ι) (a r : ι → ℝ) {x T : ℝ} (hxT : x < T)
    (h : ∀ l ∈ F, a l ≤ x → Abef F a r T - T < Abef F a r (a l) - a l) :
    ∃ t, x < t ∧ t ≤ T ∧ Wl F a r t = 0 := by
  classical
  set f : ℝ → ℝ := fun s => Abef F a r s - s with hf
  set E : Finset ℝ := insert T ((F.filter (fun k => a k ≤ T)).image a) with hE
  obtain ⟨t, htE, hmin⟩ := E.exists_min_image f ⟨T, mem_insert_self _ _⟩
  have htT : t ≤ T := by
    rcases mem_insert.1 htE with h' | h'
    · exact h'.le
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h'
      exact (mem_filter.1 hk).2
  have hft : f t ≤ f T := hmin T (mem_insert_self _ _)
  refine ⟨t, ?_, htT, ?_⟩
  · by_contra hxt
    have hxt := not_lt.1 hxt
    rcases mem_insert.1 htE with h' | h'
    · linarith
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h'
      have := h k (mem_filter.1 hk).1 hxt
      simp only [hf] at hft
      linarith
  · apply le_antisymm _ (Wl_nonneg F a r t)
    rw [Wl_le_iff]
    refine ⟨le_rfl, fun k hk hkt => ?_⟩
    have hkE : a k ∈ E :=
      mem_insert_of_mem (mem_image.2 ⟨k, mem_filter.2 ⟨hk, le_trans hkt.le htT⟩, rfl⟩)
    have := hmin _ hkE
    rw [Ain_eq_Abef_sub F a r hkt.le]
    simp only [hf] at this
    linarith

open Classical in
/-- Q2: if job `j` (requirement `> 0`, not in `G`) is finished at `t > a j`, in the sense
`Wl (insert j G) t = Wl G t`, then `insert j G` empties at some `s ∈ (a j, t]`. -/
theorem exists_Wl_insert_zero (G : Finset ι) (a r : ι → ℝ) {j : ι} (hj : j ∉ G) (hrj : 0 < r j)
    {t : ℝ} (hjt : a j < t) (hdone : Wl (insert j G) a r t = Wl G a r t) :
    ∃ s, a j < s ∧ s ≤ t ∧ Wl (insert j G) a r s = 0 := by
  classical
  set f : ℝ → ℝ := fun s => Abef G a r s - s with hf
  set Q : Finset ℝ := insert t ((G.filter (fun k => a k < t)).image a) with hQ
  obtain ⟨q, hqQ, hmin⟩ := Q.exists_min_image f ⟨t, mem_insert_self _ _⟩
  have hqt : q ≤ t := by
    rcases mem_insert.1 hqQ with h' | h'
    · exact h'.le
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h'
      exact (mem_filter.1 hk).2.le
  have hWG : Wl G a r t ≤ f t - f q := by
    rw [Wl_le_iff]
    refine ⟨by have := hmin t (mem_insert_self _ _); linarith, fun k hk hkt => ?_⟩
    have := hmin (a k) (mem_insert_of_mem (mem_image.2 ⟨k, mem_filter.2 ⟨hk, hkt⟩, rfl⟩))
    rw [Ain_eq_Abef_sub G a r hkt.le]
    simp only [hf] at this ⊢
    linarith
  have hlow : ∀ k ∈ insert j G, a k ≤ a j → f q + r j ≤ f (a k) := by
    intro k hk hkj
    have h1 := term_le_Wl (insert j G) a r t k hk (lt_of_le_of_lt hkj hjt)
    rw [Ain_eq_Abef_sub _ a r (lt_of_le_of_lt hkj hjt).le, Abef_insert hj, Abef_insert hj,
      if_pos hjt, if_neg (not_lt.2 hkj), hdone] at h1
    simp only [hf] at hWG ⊢
    linarith
  have hqj : a j < q := by
    by_contra hc
    have hc := not_lt.1 hc
    rcases mem_insert.1 hqQ with h' | h'
    · rw [h'] at hc; linarith
    · obtain ⟨k, hk, hkq⟩ := mem_image.1 h'
      have := hlow k (mem_insert_of_mem (mem_filter.1 hk).1) (by rw [hkq]; exact hc)
      rw [hkq] at this
      linarith
  refine ⟨q, hqj, hqt, le_antisymm ?_ (Wl_nonneg _ a r q)⟩
  rw [Wl_le_iff]
  refine ⟨le_rfl, fun k hk hkq => ?_⟩
  rw [Ain_eq_Abef_sub _ a r hkq.le, Abef_insert hj, Abef_insert hj, if_pos hqj]
  by_cases hkj : a k ≤ a j
  · rw [if_neg (not_lt.2 hkj)]
    have := hlow k hk hkj
    simp only [hf] at this
    linarith
  · rw [if_pos (lt_of_not_ge hkj)]
    have hkG : k ∈ G := by
      rcases mem_insert.1 hk with h' | h'
      · exact absurd (show a k ≤ a j by rw [h']) hkj
      · exact h'
    have := hmin (a k) (mem_insert_of_mem
      (mem_image.2 ⟨k, mem_filter.2 ⟨hkG, lt_of_lt_of_le hkq hqt⟩, rfl⟩))
    simp only [hf] at this
    linarith

/-- Q3: embedding a job family, shifted in time by `c`, into a bigger family can only raise the
workload. -/
theorem Wl_le_of_embed {ι' : Type*} (G' : Finset ι') (G : Finset ι) (a' r' : ι' → ℝ)
    (a r : ι → ℝ) (φ : ι' → ι) (hφ : Set.InjOn φ G') (hmaps : ∀ l ∈ G', φ l ∈ G) (c : ℝ)
    (ha : ∀ l ∈ G', a (φ l) = a' l + c) (hrr : ∀ l ∈ G', r (φ l) = r' l)
    (hr : ∀ l ∈ G, 0 ≤ r l) (s : ℝ) :
    Wl G' a' r' s ≤ Wl G a r (s + c) := by
  classical
  rw [Wl_le_iff]
  refine ⟨Wl_nonneg _ _ _ _, fun k hk hks => ?_⟩
  have hk' : a (φ k) < s + c := by rw [ha k hk]; linarith
  refine le_trans ?_ (term_le_Wl G a r (s + c) (φ k) (hmaps k hk) hk')
  rw [ha k hk]
  have : Ain G' a' r' (a' k) s ≤ Ain G a r (a' k + c) (s + c) := by
    unfold Ain
    calc ∑ l ∈ G'.filter (fun l => a' k ≤ a' l ∧ a' l < s), r' l
        = ∑ l ∈ G'.filter (fun l => a' k ≤ a' l ∧ a' l < s), r (φ l) :=
          sum_congr rfl fun l hl => (hrr l (mem_filter.1 hl).1).symm
      _ = ∑ m ∈ (G'.filter (fun l => a' k ≤ a' l ∧ a' l < s)).image φ, r m := by
          refine (sum_image ?_).symm
          intro x hx y hy hxy
          exact hφ (mem_coe.2 (mem_filter.1 hx).1) (mem_coe.2 (mem_filter.1 hy).1) hxy
      _ ≤ ∑ m ∈ G.filter (fun m => a' k + c ≤ a m ∧ a m < s + c), r m := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun m hm _ => hr m (mem_filter.1 hm).1
          intro m hm
          obtain ⟨l, hl, rfl⟩ := mem_image.1 hm
          have hl' := mem_filter.1 hl
          refine mem_filter.2 ⟨hmaps l hl'.1, ?_, ?_⟩ <;> rw [ha l hl'.1] <;>
            linarith [hl'.2.1, hl'.2.2]
  linarith

end CMQ

namespace CMR

/-- R1: arrival times of the restarted stream. -/
lemma psum_postK (t : ℝ) (k : ℕ) (x : ℕ → ℝ) (m : ℕ) :
    psum (postK t k x) (m + 1) = psum x (k + m + 1) - t := by
  induction m with
  | zero => simp [psum, postK]
  | succ m ih =>
    unfold psum at ih ⊢
    rw [Finset.sum_range_succ, ih]
    simp only [postK, if_neg (Nat.succ_ne_zero m)]
    rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, Finset.sum_range_succ _ (k + m + 1),
      show k + (m + 1) = k + m + 1 by omega]
    ring

end CMR


/-! P3b (Mathlib part) for e14b429d: the platform's arrival / schedule / departure / response time
replicated on `CMT.Om M E` (the platform's `Omega M` is `CMT.Om M (ℕ → unitInterval)` by `rfl`),
and the one-step monotone coupling `respO (i,n) (thO i ω) ≤ respO (i,n+1) ω`.
Needs D1 (CMQ), P2a (CMR), P2b (CMT), P3 (CMQ Q1-Q3, CMR.psum_postK). -/

set_option autoImplicit false

open MeasureTheory Set Finset

namespace CMV
open CMQ

variable {M : ℕ} {E : Type*}

def arrO (ω : CMT.Om M E) (j : Fin M × ℕ) : ℝ := ∑ m ∈ range (j.2 + 1), ω.1 (j.1, m)
def reqO (ω : CMT.Om M E) (j : Fin M × ℕ) : ℝ := ω.2.1 j
def keyO (σ : Equiv.Perm (Fin M)) (j : Fin M × ℕ) : Lex (Fin M × ℕ) := toLex (σ.symm j.1, j.2)
def FNO (M : ℕ) (N : ℕ) : Finset (Fin M × ℕ) := Finset.univ ×ˢ Finset.range N
noncomputable def schO (σ : Equiv.Perm (Fin M)) (ω : CMT.Om M E) (t : ℝ) : Option (Fin M × ℕ) :=
  Sch (keyO σ) (FNO M) (arrO ω) (reqO ω) t
noncomputable def depO (σ : Equiv.Perm (Fin M)) (j : Fin M × ℕ) (ω : CMT.Om M E) : ℝ :=
  sInf {t : ℝ | reqO ω j ≤ servedG (schO σ ω) j t}
noncomputable def respO (σ : Equiv.Perm (Fin M)) (j : Fin M × ℕ) (ω : CMT.Om M E) : ℝ :=
  depO σ j ω - arrO ω j

def GoodO (ω : CMT.Om M E) : Prop :=
  (∀ j, 0 < ω.1 j) ∧ (∀ j, 0 < ω.2.1 j) ∧ ∀ T : ℝ, ∃ N0 : ℕ, ∀ l, arrO ω l ≤ T → l.2 < N0

lemma keyO_inj (σ : Equiv.Perm (Fin M)) : Function.Injective (keyO σ) := by
  intro j j' h
  unfold keyO at h
  have h2 := toLex.injective h
  simp only [Prod.mk.injEq] at h2
  exact Prod.ext (σ.symm.injective h2.1) h2.2

lemma FNO_mono (M : ℕ) : Monotone (FNO M) := by
  intro N N' h j hj
  simp only [FNO, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hj ⊢
  omega

lemma mem_FNO {N : ℕ} {j : Fin M × ℕ} : j ∈ FNO M N ↔ j.2 < N := by simp [FNO]

lemma arrO_nonneg {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (j : Fin M × ℕ) : 0 ≤ arrO ω j :=
  sum_nonneg fun _ _ => (h _).le

lemma covers_of_good {ω : CMT.Om M E} (hω : GoodO ω) (T : ℝ) :
    ∃ N0, Covers (FNO M) (arrO ω) N0 T := by
  obtain ⟨N0, h⟩ := hω.2.2 T
  exact ⟨N0, fun l hl => mem_FNO.2 (h l hl)⟩

lemma covers_mono {ω : CMT.Om M E} {N0 N1 : ℕ} {T T' : ℝ} (hc : Covers (FNO M) (arrO ω) N0 T)
    (hN : N0 ≤ N1) (hT : T' ≤ T) : Covers (FNO M) (arrO ω) N1 T' :=
  fun l hl => FNO_mono M hN (hc l (le_trans hl hT))

lemma servedG_nonpos (S : ℝ → Option (Fin M × ℕ)) (j : Fin M × ℕ) {t : ℝ} (ht : t ≤ 0) :
    servedG S j t = 0 := by
  unfold servedG
  rw [Ico_eq_empty (not_lt.2 ht), inter_empty, measure_empty, ENNReal.toReal_zero]

variable (σ : Equiv.Perm (Fin M))

lemma served_eq {ω : CMT.Om M E} (hω : GoodO ω) {N0 : ℕ} {t : ℝ}
    (hc : Covers (FNO M) (arrO ω) N0 t) (j : Fin M × ℕ) :
    servedG (schO σ ω) j t = (if arrO ω j < t then reqO ω j else 0) -
      (Wl (Le (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t -
        Wl (Lt (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t) :=
  served_formula (keyO_inj σ) (FNO_mono M) (arrO_nonneg hω.1) hω.2.1 hc j

lemma Wl_Lt_le {ω : CMT.Om M E} (hω : GoodO ω) (N : ℕ) (j : Fin M × ℕ) (t : ℝ) :
    Wl (Lt (keyO σ) (FNO M) N j) (arrO ω) (reqO ω) t ≤
      Wl (Le (keyO σ) (FNO M) N j) (arrO ω) (reqO ω) t :=
  Wl_mono (Lt_sub_Le N j) (fun l _ => (hω.2.1 l).le) t

lemma done_imp {ω : CMT.Om M E} (hω : GoodO ω) {N0 : ℕ} {t : ℝ}
    (hc : Covers (FNO M) (arrO ω) N0 t) {j : Fin M × ℕ}
    (h : reqO ω j ≤ servedG (schO σ ω) j t) :
    arrO ω j < t ∧ Wl (Le (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t =
      Wl (Lt (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t := by
  rw [served_eq σ hω hc j] at h
  have hle := Wl_Lt_le σ hω N0 j t
  have hr : 0 < reqO ω j := hω.2.1 j
  split_ifs at h with hlt
  · exact ⟨hlt, by linarith⟩
  · exfalso; linarith

lemma done_of {ω : CMT.Om M E} (hω : GoodO ω) {N0 : ℕ} {t : ℝ}
    (hc : Covers (FNO M) (arrO ω) N0 t) {j : Fin M × ℕ} (hlt : arrO ω j < t)
    (h0 : Wl (Le (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t = 0) :
    reqO ω j ≤ servedG (schO σ ω) j t := by
  rw [served_eq σ hω hc j, if_pos hlt, h0]
  have hle := Wl_Lt_le σ hω N0 j t
  have h1 := Wl_nonneg (Lt (keyO σ) (FNO M) N0 j) (arrO ω) (reqO ω) t
  rw [h0] at hle
  linarith

/-! ### the shift `thO i` on job coordinates -/

variable (i : Fin M)

lemma thO_fst_i (ω : CMT.Om M E) (m : ℕ) : (CMT.thO i ω).1 (i, m) = ω.1 (i, m + 1) := by
  show (CMT.thS i (CMT.toS ω) i).1 m = _
  simp only [CMT.thS]
  show ω.1 (i, 1 + m) = _
  rw [add_comm]

lemma thO_fst_k (ω : CMT.Om M E) {k : Fin M} (hk : k ≠ i) (m : ℕ) :
    (CMT.thO i ω).1 (k, m) = CMR.post (ω.1 (i, 0)) (fun l => ω.1 (k, l)) m := by
  show (CMT.thS i (CMT.toS ω) k).1 m = _
  simp only [CMT.thS, if_neg hk]
  rfl

lemma thO_req_i (ω : CMT.Om M E) (m : ℕ) : (CMT.thO i ω).2.1 (i, m) = ω.2.1 (i, m + 1) := by
  show (CMT.thS i (CMT.toS ω) i).2.1 m = _
  simp only [CMT.thS]
  show ω.2.1 (i, 1 + m) = _
  rw [add_comm]

lemma thO_req_k (ω : CMT.Om M E) {k : Fin M} (hk : k ≠ i) (m : ℕ) :
    (CMT.thO i ω).2.1 (k, m) =
      ω.2.1 (k, CMR.Nidx (ω.1 (i, 0)) (fun l => ω.1 (k, l)) + m) := by
  show (CMT.thS i (CMT.toS ω) k).2.1 m = _
  simp only [CMT.thS, if_neg hk]
  rfl

/-- the number of class-`k` arrivals in `[0, T0]`. -/
noncomputable def Nk (ω : CMT.Om M E) (k : Fin M) : ℕ := CMR.Nidx (ω.1 (i, 0)) (fun l => ω.1 (k, l))

lemma ev_exists {x : ℕ → ℝ} {T : ℝ} (hfin : ∃ m, T < CMR.psum x (m + 1)) : ∃ N, CMR.Ev T N x := by
  classical
  exact ⟨Nat.find hfin, fun j hj => not_lt.1 (Nat.find_min hfin hj), Nat.find_spec hfin⟩

lemma ev_Nk {ω : CMT.Om M E} (hω : GoodO ω) (k : Fin M) :
    CMR.Ev (ω.1 (i, 0)) (Nk i ω k) (fun l => ω.1 (k, l)) := by
  obtain ⟨N0, h⟩ := hω.2.2 (ω.1 (i, 0))
  obtain ⟨N, hN⟩ := ev_exists (x := fun l => ω.1 (k, l)) (T := ω.1 (i, 0))
    ⟨N0, lt_of_not_ge fun hc => lt_irrefl N0 (h (k, N0) hc)⟩
  unfold Nk
  rw [CMR.Nidx_eq hN]
  exact hN

lemma arr_thO_i (ω : CMT.Om M E) (m : ℕ) :
    arrO (CMT.thO i ω) (i, m) = arrO ω (i, m + 1) - ω.1 (i, 0) := by
  unfold arrO
  simp only [thO_fst_i]
  have := Finset.sum_range_succ' (fun l => ω.1 (i, l)) (m + 1)
  linarith

lemma arr_thO_k {ω : CMT.Om M E} (hω : GoodO ω) {k : Fin M} (hk : k ≠ i) (m : ℕ) :
    arrO (CMT.thO i ω) (k, m) = arrO ω (k, Nk i ω k + m) - ω.1 (i, 0) := by
  unfold arrO
  simp only [thO_fst_k i ω hk]
  show CMR.psum (CMR.post (ω.1 (i, 0)) (fun l => ω.1 (k, l))) (m + 1) =
    CMR.psum (fun l => ω.1 (k, l)) (Nk i ω k + m + 1) - ω.1 (i, 0)
  unfold CMR.post
  rw [CMR.Nidx_eq (ev_Nk i hω k), CMR.psum_postK]

/-- the job map: job `l` of `thO i ω` is job `phi l` of `ω`. -/
noncomputable def phi (ω : CMT.Om M E) (l : Fin M × ℕ) : Fin M × ℕ :=
  if l.1 = i then (i, l.2 + 1) else (l.1, Nk i ω l.1 + l.2)

lemma phi_fst (ω : CMT.Om M E) (l : Fin M × ℕ) : (phi i ω l).1 = l.1 := by
  unfold phi; split_ifs with h
  · exact h.symm
  · rfl

lemma phi_snd_ge (ω : CMT.Om M E) (l : Fin M × ℕ) : l.2 ≤ (phi i ω l).2 := by
  unfold phi; split_ifs <;> simp

lemma phi_inj (ω : CMT.Om M E) : Function.Injective (phi i ω) := by
  intro l l' h
  have h1 : l.1 = l'.1 := by rw [← phi_fst i ω l, ← phi_fst i ω l', h]
  obtain ⟨k, m⟩ := l
  obtain ⟨k', m'⟩ := l'
  simp only at h1
  subst h1
  unfold phi at h
  simp only at h
  split_ifs at h with hk
  · simp only [Prod.mk.injEq, add_left_inj] at h; rw [h.2]
  · simp only [Prod.mk.injEq, add_right_inj] at h; rw [h.2]

lemma arrO_phi {ω : CMT.Om M E} (hω : GoodO ω) (l : Fin M × ℕ) :
    arrO ω (phi i ω l) = arrO (CMT.thO i ω) l + ω.1 (i, 0) := by
  obtain ⟨k, m⟩ := l
  by_cases hk : k = i
  · subst hk
    rw [phi, if_pos rfl, arr_thO_i]; ring
  · simp only [phi, if_neg hk]
    rw [arr_thO_k i hω hk m]; ring

lemma reqO_phi (ω : CMT.Om M E) (l : Fin M × ℕ) :
    reqO ω (phi i ω l) = reqO (CMT.thO i ω) l := by
  obtain ⟨k, m⟩ := l
  by_cases hk : k = i
  · subst hk
    rw [phi, if_pos rfl]
    unfold reqO; rw [thO_req_i]
  · simp only [phi, if_neg hk]
    unfold reqO; rw [thO_req_k i ω hk]; rfl

lemma good_thO {ω : CMT.Om M E} (hω : GoodO ω) : GoodO (CMT.thO i ω) := by
  refine ⟨fun l => ?_, fun l => ?_, fun T => ?_⟩
  · obtain ⟨k, m⟩ := l
    by_cases hk : k = i
    · subst hk; rw [thO_fst_i]; exact hω.1 _
    · rw [thO_fst_k i ω hk]
      unfold CMR.post
      rw [show CMR.Nidx (ω.1 (i, 0)) (fun l => ω.1 (k, l)) = Nk i ω k from rfl]
      unfold CMR.postK
      split_ifs with hm
      · have := (ev_Nk i hω k).2; linarith
      · exact hω.1 _
  · have := hω.2.1 (phi i ω l)
    rwa [show ω.2.1 (phi i ω l) = reqO ω (phi i ω l) from rfl, reqO_phi] at this
  · obtain ⟨N0, h⟩ := hω.2.2 (T + ω.1 (i, 0))
    refine ⟨N0, fun l hl => ?_⟩
    have := h (phi i ω l) (by rw [arrO_phi i hω l]; linarith)
    exact lt_of_le_of_lt (phi_snd_ge i ω l) this

/-! ### V2: the monotone coupling -/

lemma key_phi (ω : CMT.Om M E) {l : Fin M × ℕ} {n : ℕ} (h : keyO σ l ≤ keyO σ (i, n)) :
    keyO σ (phi i ω l) ≤ keyO σ (i, n + 1) := by
  obtain ⟨k, m⟩ := l
  unfold keyO at h ⊢
  rw [Prod.Lex.toLex_le_toLex] at h ⊢
  by_cases hk : k = i
  · subst hk
    rw [phi, if_pos rfl]
    simp only at h
    rcases h with h | h
    · exact absurd h (lt_irrefl _)
    · right; exact ⟨rfl, by omega⟩
  · simp only [phi, if_neg hk]
    simp only at h ⊢
    rcases h with h | h
    · left; exact h
    · exact absurd (σ.symm.injective h.1) hk

theorem resp_thO_le {ω : CMT.Om M E} (hω : GoodO ω) (n : ℕ)
    (hcomp : ∃ t, reqO ω (i, n + 1) ≤ servedG (schO σ ω) (i, n + 1) t) :
    respO σ (i, n) (CMT.thO i ω) ≤ respO σ (i, n + 1) ω := by
  have hω' := good_thO i hω
  set T0 := ω.1 (i, 0) with hT0
  set ω' := CMT.thO i ω with hω'def
  have harr : arrO ω (i, n + 1) = arrO ω' (i, n) + T0 := by
    have := arrO_phi i hω (i, n)
    rw [phi, if_pos rfl] at this
    exact this
  have hreq : reqO ω (i, n + 1) = reqO ω' (i, n) := by
    have := reqO_phi i ω (i, n)
    rw [phi, if_pos rfl] at this
    exact this
  set A := {t : ℝ | reqO ω (i, n + 1) ≤ servedG (schO σ ω) (i, n + 1) t} with hA
  set A' := {t : ℝ | reqO ω' (i, n) ≤ servedG (schO σ ω') (i, n) t} with hA'
  have hA'bdd : BddBelow A' := by
    refine ⟨0, fun t ht => ?_⟩
    by_contra hc
    have h0 := servedG_nonpos (schO σ ω') (i, n) (le_of_lt (lt_of_not_ge hc))
    have hr := hω'.2.1 (i, n)
    simp only [hA', mem_setOf_eq, h0] at ht
    unfold reqO at ht
    linarith
  have hmap : ∀ t ∈ A, t - T0 ∈ A' := by
    intro t ht
    obtain ⟨N0, hc⟩ := covers_of_good hω t
    obtain ⟨N0', hc'⟩ := covers_of_good hω' (t - T0)
    set N1 := max N0 (N0' + 1 + ∑ k, Nk i ω k) with hN1
    have hc1 : Covers (FNO M) (arrO ω) N1 t := covers_mono hc (le_max_left _ _) le_rfl
    obtain ⟨hlt, hdone⟩ := done_imp σ hω hc1 ht
    have hjmem : (i, n + 1) ∈ FNO M N1 := hc1 _ hlt.le
    rw [Le_eq_insert (keyO_inj σ) hjmem] at hdone
    obtain ⟨s, hjs, hst, hWs⟩ := exists_Wl_insert_zero (Lt (keyO σ) (FNO M) N1 (i, n + 1))
      (arrO ω) (reqO ω) (notmem_Lt N1 (i, n + 1)) (hω.2.1 _) hlt hdone
    rw [← Le_eq_insert (keyO_inj σ) hjmem] at hWs
    have hQ3 := Wl_le_of_embed (Le (keyO σ) (FNO M) N0' (i, n)) (Le (keyO σ) (FNO M) N1 (i, n + 1))
      (arrO ω') (reqO ω') (arrO ω) (reqO ω) (phi i ω) ((phi_inj i ω).injOn)
      (fun l hl => by
        simp only [Le, mem_filter] at hl ⊢
        refine ⟨?_, key_phi σ i ω hl.2⟩
        rw [mem_FNO] at hl ⊢
        have h1 := hl.1
        have h2 : (phi i ω l).2 ≤ l.2 + 1 + ∑ k, Nk i ω k := by
          unfold phi
          split_ifs
          · show l.2 + 1 ≤ _
            omega
          · show Nk i ω l.1 + l.2 ≤ _
            have := Finset.single_le_sum (f := fun k => Nk i ω k) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ l.1)
            omega
        have h3 : (phi i ω l).2 < N0' + 1 + ∑ k, Nk i ω k := by omega
        exact lt_of_lt_of_le h3 (le_max_right _ _))
      T0 (fun l _ => arrO_phi i hω l) (fun l _ => reqO_phi i ω l)
      (fun l _ => (hω.2.1 l).le) (s - T0)
    rw [sub_add_cancel, hWs] at hQ3
    have hz : Wl (Le (keyO σ) (FNO M) N0' (i, n)) (arrO ω') (reqO ω') (s - T0) = 0 :=
      le_antisymm hQ3 (Wl_nonneg _ _ _ _)
    have hc's : Covers (FNO M) (arrO ω') N0' (s - T0) := covers_mono hc' le_rfl (by linarith)
    have hlt' : arrO ω' (i, n) < s - T0 := by linarith
    have hserv := done_of σ hω' hc's hlt' hz
    exact le_trans hserv (servedG_mono _ _ (by linarith))
  have hAne : A.Nonempty := hcomp
  have hdep : depO σ (i, n) ω' + T0 ≤ depO σ (i, n + 1) ω := by
    refine le_csInf hAne fun t ht => ?_
    have := csInf_le hA'bdd (hmap t ht)
    show sInf A' + T0 ≤ t
    linarith
  unfold respO
  linarith

/-! ### V1 part 1: identification of the windows along the orbit of `thO i` -/

/-- other-class work of `ω` with arrival in `(u, v]`, truncated to `FNO M N`. -/
noncomputable def Oth (ω : CMT.Om M E) (N : ℕ) (u v : ℝ) : ℝ :=
  ∑ l ∈ (FNO M N).filter (fun l => l.1 ≠ i ∧ u < arrO ω l ∧ arrO ω l ≤ v), reqO ω l

/-- the class-`i` epoch before window `m` (`0` for the first window). -/
noncomputable def Tlow (ω : CMT.Om M E) (m : ℕ) : ℝ := if m = 0 then 0 else arrO ω (i, m - 1)

lemma arrO_mono {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (k : Fin M) {m m' : ℕ} (hm : m ≤ m') :
    arrO ω (k, m) ≤ arrO ω (k, m') :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun _ _ _ => (h _).le)

lemma arrO_pos {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (l : Fin M × ℕ) : 0 < arrO ω l :=
  sum_pos (fun _ _ => h _) nonempty_range_add_one

lemma arr_le_T0_iff {ω : CMT.Om M E} (hω : GoodO ω) (k : Fin M) (m : ℕ) :
    arrO ω (k, m) ≤ ω.1 (i, 0) ↔ m < Nk i ω k := by
  have hev := ev_Nk i hω k
  constructor
  · intro h
    by_contra hc
    have h1 := arrO_mono hω.1 k (not_lt.1 hc)
    have h2 : ω.1 (i, 0) < arrO ω (k, Nk i ω k) := hev.2
    linarith
  · intro h
    exact hev.1 m h

lemma phi_ne (ω : CMT.Om M E) {l : Fin M × ℕ} (hl : l.1 ≠ i) :
    phi i ω l = (l.1, Nk i ω l.1 + l.2) := by
  unfold phi; rw [if_neg hl]

lemma Oth_shift {ω : CMT.Om M E} (hω : GoodO ω) {N N' : ℕ} {u v : ℝ} (hu : 0 ≤ u)
    (hc : Covers (FNO M) (arrO ω) N (v + ω.1 (i, 0)))
    (hc' : Covers (FNO M) (arrO (CMT.thO i ω)) N' v) :
    Oth i (CMT.thO i ω) N' u v = Oth i ω N (u + ω.1 (i, 0)) (v + ω.1 (i, 0)) := by
  unfold Oth
  refine Finset.sum_nbij' (phi i ω) (fun q => (q.1, q.2 - Nk i ω q.1)) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter] at hl ⊢
    have ha := arrO_phi i hω l
    refine ⟨hc _ (by rw [ha]; linarith [hl.2.2.2]), by rw [phi_fst]; exact hl.2.1,
      by rw [ha]; linarith [hl.2.2.1], by rw [ha]; linarith [hl.2.2.2]⟩
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    have hge : Nk i ω q.1 ≤ q.2 := by
      by_contra hcon
      have := (arr_le_T0_iff i hω q.1 q.2).2 (lt_of_not_ge hcon)
      linarith [hq.2.2.1]
    have hpq : phi i ω (q.1, q.2 - Nk i ω q.1) = q := by
      rw [phi_ne i ω (show (q.1, q.2 - Nk i ω q.1).1 ≠ i from hq.2.1)]
      ext
      · rfl
      · simp only; omega
    have ha := arrO_phi i hω (q.1, q.2 - Nk i ω q.1)
    rw [hpq] at ha
    refine ⟨hc' _ (by linarith [hq.2.2.2]), hq.2.1, by linarith [hq.2.2.1],
      by linarith [hq.2.2.2]⟩
  · intro l hl
    simp only [Finset.mem_filter] at hl
    rw [phi_ne i ω hl.2.1]
    ext
    · rfl
    · simp only; omega
  · intro q hq
    simp only [Finset.mem_filter] at hq
    have hge : Nk i ω q.1 ≤ q.2 := by
      by_contra hcon
      have := (arr_le_T0_iff i hω q.1 q.2).2 (lt_of_not_ge hcon)
      linarith [hq.2.2.1]
    rw [phi_ne i ω (show (q.1, q.2 - Nk i ω q.1).1 ≠ i from hq.2.1)]
    ext
    · rfl
    · simp only; omega
  · intro l _
    exact (reqO_phi i ω l).symm

lemma win0_A {ω : CMT.Om M E} (hω : GoodO ω) {N : ℕ}
    (hc : Covers (FNO M) (arrO ω) N (arrO ω (i, 0))) :
    (CMT.WinO i ω).2.1 = Oth i ω N 0 (arrO ω (i, 0)) := by
  have hT0 : arrO ω (i, 0) = ω.1 (i, 0) := by simp [arrO]
  show CMT.sumW i (ω.1 (i, 0)) (CMT.toS ω) = _
  unfold CMT.sumW Oth
  rw [Finset.sum_filter, FNO, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · rw [if_pos hk]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    rw [if_neg (by simp [hk])]
  · rw [if_neg hk, ← Finset.sum_filter]
    show ∑ m ∈ range (Nk i ω k), ω.2.1 (k, m) = _
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_range, Finset.mem_filter, ne_eq, hk, not_false_eq_true, true_and]
    constructor
    · intro hm
      have hle := (arr_le_T0_iff i hω k m).2 hm
      rw [← hT0] at hle
      exact ⟨mem_FNO.1 (hc (k, m) hle), arrO_pos hω.1 _, hle⟩
    · rintro ⟨_, _, hle⟩
      rw [hT0] at hle
      exact (arr_le_T0_iff i hω k m).1 hle

/-- the windows along the orbit: window `n` of `ω` is `(r(i,n), other work in (T_{n-1}, T_n], τ_n)`. -/
theorem win_eq (n : ℕ) : ∀ ω : CMT.Om M E, GoodO ω →
    (CMT.WinO i ((CMT.thO i)^[n] ω)).1 = ω.2.1 (i, n) ∧
    (CMT.WinO i ((CMT.thO i)^[n] ω)).2.2 = ω.1 (i, n) ∧
    ∀ N, Covers (FNO M) (arrO ω) N (arrO ω (i, n)) →
      (CMT.WinO i ((CMT.thO i)^[n] ω)).2.1 = Oth i ω N (Tlow i ω n) (arrO ω (i, n)) := by
  induction n with
  | zero =>
    intro ω hω
    refine ⟨rfl, rfl, fun N hc => ?_⟩
    rw [Function.iterate_zero, id, win0_A i hω hc]
    simp [Tlow]
  | succ n ih =>
    intro ω hω
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3⟩ := ih (CMT.thO i ω) (good_thO i hω)
    refine ⟨by rw [h1, thO_req_i], by rw [h2, thO_fst_i], fun N hc => ?_⟩
    obtain ⟨N', hc'⟩ := covers_of_good (good_thO i hω) (arrO (CMT.thO i ω) (i, n))
    rw [h3 N' hc']
    have e2 : arrO ω (i, n + 1) = arrO (CMT.thO i ω) (i, n) + ω.1 (i, 0) := by
      rw [arr_thO_i]; ring
    have e1 : Tlow i ω (n + 1) = Tlow i (CMT.thO i ω) n + ω.1 (i, 0) := by
      unfold Tlow
      rw [if_neg (Nat.succ_ne_zero n)]
      by_cases hn : n = 0
      · subst hn; simp [arrO]
      · rw [if_neg hn, arr_thO_i, show n - 1 + 1 = n by omega, show n + 1 - 1 = n by omega]
        ring
    have hu : 0 ≤ Tlow i (CMT.thO i ω) n := by
      unfold Tlow; split_ifs
      · exact le_rfl
      · exact arrO_nonneg (good_thO i hω).1 _
    rw [e1, e2]
    rw [e2] at hc
    exact Oth_shift i hω hu hc hc'

end CMV


/-! P3c (Mathlib part) for e14b429d, V1 part 2: the response time of job `(i, n)` is bounded by
the busy-period majorant `CMU.Bnd` of the window sequence along the orbit of `thO i`.
Needs D1 (CMQ), P2a (CMR), P2b (CMT), P4 (CMU), P3, P3b (CMV). -/

set_option autoImplicit false

open MeasureTheory Set Finset

namespace CMV
open CMQ

variable {M : ℕ} {E : Type*} (σ : Equiv.Perm (Fin M)) (i : Fin M)

/-- work of `FNO M N` with arrival in `(u, v]`. -/
noncomputable def Gw (ω : CMT.Om M E) (N : ℕ) (u v : ℝ) : ℝ :=
  ∑ l ∈ (FNO M N).filter (fun l => u < arrO ω l ∧ arrO ω l ≤ v), reqO ω l

lemma Gw_split (ω : CMT.Om M E) (N : ℕ) {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
    Gw ω N u w = Gw ω N u v + Gw ω N v w := by
  unfold Gw
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hl, h1, h2⟩
      by_cases h : arrO ω l ≤ v
      · exact Or.inl ⟨hl, h1, h⟩
      · exact Or.inr ⟨hl, lt_of_not_ge h, h2⟩
    · rintro (⟨hl, h1, h2⟩ | ⟨hl, h1, h2⟩)
      · exact ⟨hl, h1, by linarith⟩
      · exact ⟨hl, by linarith, h2⟩
  · rw [Finset.disjoint_filter]
    intro l _ h1 h2
    linarith [h1.2, h2.1]

lemma arrO_succ (ω : CMT.Om M E) (k : Fin M) (m : ℕ) :
    arrO ω (k, m + 1) = arrO ω (k, m) + ω.1 (k, m + 1) := by
  simp only [arrO]
  rw [Finset.sum_range_succ]

lemma arrO_add (ω : CMT.Om M E) (k : Fin M) (m L : ℕ) :
    arrO ω (k, m + L) = arrO ω (k, m) + ∑ l ∈ range L, ω.1 (k, m + 1 + l) := by
  induction L with
  | zero => simp
  | succ L ih =>
    show arrO ω (k, m + L + 1) = _
    rw [arrO_succ, ih, Finset.sum_range_succ, show m + 1 + L = m + L + 1 by omega]
    ring

lemma arrO_lt {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (k : Fin M) {m m' : ℕ} (hm : m < m') :
    arrO ω (k, m) < arrO ω (k, m') := by
  have h1 := arrO_mono h k (show m + 1 ≤ m' by omega)
  rw [arrO_succ] at h1
  linarith [h (k, m + 1)]

lemma Tlow_succ (ω : CMT.Om M E) (m : ℕ) : Tlow i ω (m + 1) = arrO ω (i, m) := by
  simp [Tlow]

lemma Tlow_lt {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (m : ℕ) : Tlow i ω m < arrO ω (i, m) := by
  cases m with
  | zero => simp only [Tlow, if_pos rfl]; exact arrO_pos h _
  | succ m => rw [Tlow_succ]; exact arrO_lt h i (Nat.lt_succ_self m)

lemma Tlow_nonneg {ω : CMT.Om M E} (h : ∀ j, 0 < ω.1 j) (m : ℕ) : 0 ≤ Tlow i ω m := by
  unfold Tlow
  split_ifs
  · exact le_rfl
  · exact arrO_nonneg h _

lemma Gw_win {ω : CMT.Om M E} (hω : GoodO ω) {N m : ℕ} (hm : m < N) :
    Gw ω N (Tlow i ω m) (arrO ω (i, m)) =
      reqO ω (i, m) + Oth i ω N (Tlow i ω m) (arrO ω (i, m)) := by
  unfold Gw Oth
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun l : Fin M × ℕ => l.1 = i)]
  congr 1
  · rw [Finset.filter_filter, Finset.sum_eq_single (i, m)]
    · intro b hb hne
      exfalso
      simp only [mem_filter] at hb
      obtain ⟨_, ⟨h1, h2⟩, h3⟩ := hb
      obtain ⟨b1, b2⟩ := b
      simp only at h3
      rw [h3] at h1 h2 hne
      apply hne
      rcases lt_trichotomy b2 m with hlt | heq | hgt
      · exfalso
        have hm1 : m = (m - 1) + 1 := by omega
        have hT : Tlow i ω m = arrO ω (i, m - 1) := by
          rw [hm1, Tlow_succ]; simp
        have := arrO_mono hω.1 i (show b2 ≤ m - 1 by omega)
        linarith
      · rw [heq]
      · exfalso
        have := arrO_lt hω.1 i hgt
        linarith
    · intro hnot
      exfalso
      apply hnot
      simp only [mem_filter, mem_FNO]
      exact ⟨hm, ⟨Tlow_lt i hω.1 m, le_rfl⟩, trivial⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [mem_filter, ne_eq]
    tauto

lemma Gw_sum {ω : CMT.Om M E} (hω : GoodO ω) {N k : ℕ} :
    ∀ m, k ≤ m → m < N →
      Gw ω N (Tlow i ω k) (arrO ω (i, m)) =
        ∑ q ∈ Icc k m, (reqO ω (i, q) + Oth i ω N (Tlow i ω q) (arrO ω (i, q))) := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base =>
    intro hk
    rw [Finset.Icc_self, Finset.sum_singleton, Gw_win i hω hk]
  | succ m hkm ih =>
    intro hm
    have hTk : Tlow i ω k ≤ arrO ω (i, m) :=
      le_trans (Tlow_lt i hω.1 k).le (arrO_mono hω.1 i hkm)
    rw [Gw_split ω N hTk (arrO_mono hω.1 i (Nat.le_succ m)), ih (by omega),
      Finset.sum_Icc_succ_top (by omega), ← Tlow_succ i ω m, Gw_win i hω hm]

lemma sum_Icc_eq (f : ℕ → ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∑ q ∈ Icc k m, f q = f k + ∑ l ∈ range (m - k), f (k + 1 + l) := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, show m + 1 - k = m - k + 1 by omega,
      Finset.sum_range_succ, show k + 1 + (m - k) = m + 1 by omega]
    ring

lemma Abef_sub_le {ω : CMT.Om M E} (hω : GoodO ω) (N : ℕ) {u x T : ℝ} (hux : u < x) :
    Abef (FNO M N) (arrO ω) (reqO ω) T - Abef (FNO M N) (arrO ω) (reqO ω) x ≤ Gw ω N u T := by
  unfold Abef Gw
  set A := (FNO M N).filter (fun l => u < arrO ω l ∧ arrO ω l ≤ T)
  set B := (FNO M N).filter (fun l => arrO ω l < x)
  have hsub : (FNO M N).filter (fun l => arrO ω l < T) ⊆ A ∪ B := by
    intro l hl
    simp only [A, B, Finset.mem_filter, Finset.mem_union] at hl ⊢
    by_cases h : arrO ω l < x
    · exact Or.inr ⟨hl.1, h⟩
    · exact Or.inl ⟨hl.1, by linarith [not_lt.1 h], hl.2.le⟩
  have h1 : ∑ l ∈ (FNO M N).filter (fun l => arrO ω l < T), reqO ω l ≤ ∑ l ∈ A ∪ B, reqO ω l :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => (hω.2.1 l).le)
  have h2 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := reqO ω)
  have h3 : 0 ≤ ∑ l ∈ A ∩ B, reqO ω l := Finset.sum_nonneg fun l _ => (hω.2.1 l).le
  linarith

/-- the window sequence along the orbit of `thO i`. -/
noncomputable def wsO (ω : CMT.Om M E) (m : ℕ) : ℝ × ℝ × ℝ := CMT.WinO i ((CMT.thO i)^[m] ω)

lemma Oth_nonneg {ω : CMT.Om M E} (hω : GoodO ω) (N : ℕ) (u v : ℝ) : 0 ≤ Oth i ω N u v :=
  Finset.sum_nonneg fun l _ => (hω.2.1 l).le

lemma Xb_nonneg {ω : CMT.Om M E} (hω : GoodO ω) (n : ℕ) : 0 ≤ CMU.Xb (wsO i ω) n := by
  obtain ⟨N, hc⟩ := covers_of_good hω (arrO ω (i, n))
  obtain ⟨h1, -, h3⟩ := win_eq i n ω hω
  have hle : (wsO i ω n).1 + (wsO i ω n).2.1 + CMU.Sy (wsO i ω) n (n - n) ≤ CMU.Xb (wsO i ω) n :=
    Finset.le_sup' (fun k => (wsO i ω k).1 + (wsO i ω k).2.1 + CMU.Sy (wsO i ω) k (n - k))
      (Finset.mem_range.2 n.lt_succ_self)
  have hS : CMU.Sy (wsO i ω) n (n - n) = 0 := by simp [CMU.Sy]
  have e1 : (wsO i ω n).1 = ω.2.1 (i, n) := h1
  have e2 : (wsO i ω n).2.1 = Oth i ω N (Tlow i ω n) (arrO ω (i, n)) := h3 N hc
  rw [hS, e1, e2] at hle
  linarith [hω.2.1 (i, n), Oth_nonneg i hω N (Tlow i ω n) (arrO ω (i, n))]

/-- V1 (b): a negative Lindley drift after window `n` forces the system to empty in
`(T_n, T_{n+K}]`. -/
theorem empties {ω : CMT.Om M E} (hω : GoodO ω) {n K N : ℕ} (hK : 0 < K)
    (hc : Covers (FNO M) (arrO ω) N (arrO ω (i, n + K)))
    (hneg : CMU.Xb (wsO i ω) n + CMU.Sy (wsO i ω) n K < 0) :
    ∃ t, arrO ω (i, n) < t ∧ t ≤ arrO ω (i, n + K) ∧ Wl (FNO M N) (arrO ω) (reqO ω) t = 0 := by
  classical
  have hNK : n + K < N := mem_FNO.1 (hc (i, n + K) le_rfl)
  refine exists_Wl_zero_drift (FNO M N) (arrO ω) (reqO ω) (arrO_lt hω.1 i (by omega)) ?_
  intro l _ hl
  have hex : ∃ k, arrO ω l ≤ arrO ω (i, k) := ⟨n, hl⟩
  set k := Nat.find hex with hkdef
  have hk : arrO ω l ≤ arrO ω (i, k) := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex hl
  have hlow : Tlow i ω k < arrO ω l := by
    unfold Tlow
    split_ifs with hk0
    · exact arrO_pos hω.1 l
    · have := Nat.find_min hex (show k - 1 < k by omega)
      exact lt_of_not_ge this
  have hA := Abef_sub_le hω N (T := arrO ω (i, n + K)) hlow
  rw [Gw_sum i hω (n + K) (by omega) hNK] at hA
  rw [sum_Icc_eq _ (show k ≤ n + K by omega)] at hA
  -- identify the windows
  have hw : ∀ q, q ≤ n + K → (wsO i ω q).1 = reqO ω (i, q) ∧ (wsO i ω q).2.2 = ω.1 (i, q) ∧
      (wsO i ω q).2.1 = Oth i ω N (Tlow i ω q) (arrO ω (i, q)) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := win_eq i q ω hω
    exact ⟨h1, h2, h3 N (covers_mono hc le_rfl (arrO_mono hω.1 i hq))⟩
  have hT := arrO_add ω i k (n + K - k)
  rw [show k + (n + K - k) = n + K by omega] at hT
  have hX : (wsO i ω k).1 + (wsO i ω k).2.1 + CMU.Sy (wsO i ω) k (n - k) ≤ CMU.Xb (wsO i ω) n :=
    Finset.le_sup' (fun k => (wsO i ω k).1 + (wsO i ω k).2.1 + CMU.Sy (wsO i ω) k (n - k))
      (Finset.mem_range.2 (by omega))
  have hadd := CMU.Sy_add (wsO i ω) hkn K
  rw [show n - k + K = n + K - k by omega] at hadd
  have hSy : CMU.Sy (wsO i ω) k (n + K - k) =
      ∑ l ∈ range (n + K - k), (reqO ω (i, k + 1 + l) +
        Oth i ω N (Tlow i ω (k + 1 + l)) (arrO ω (i, k + 1 + l))) -
      ∑ l ∈ range (n + K - k), ω.1 (i, k + 1 + l) := by
    unfold CMU.Sy
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hq := hw (k + 1 + l) (by have := Finset.mem_range.1 hl; omega)
    rw [hq.1, hq.2.1, hq.2.2]
  obtain ⟨hk1, -, hk3⟩ := hw k (by omega)
  rw [hk1, hk3] at hX
  linarith

/-- the majorant dominates the time until the first emptying window. -/
lemma Bnd_ge {ω : CMT.Om M E} (hω : GoodO ω) (n L : ℕ)
    (hL : ∀ K < L, 0 ≤ CMU.Xb (wsO i ω) n + CMU.Sy (wsO i ω) n K) :
    ENNReal.ofReal (arrO ω (i, n + L) - arrO ω (i, n)) ≤ CMU.Bnd (wsO i ω) n := by
  have hT := arrO_add ω i n L
  rw [show arrO ω (i, n + L) - arrO ω (i, n) = ∑ l ∈ range L, ω.1 (i, n + 1 + l) by linarith,
    ENNReal.ofReal_sum_of_nonneg (fun l _ => (hω.1 _).le)]
  unfold CMU.Bnd
  refine le_trans ?_ (ENNReal.sum_le_tsum (range L))
  refine Finset.sum_le_sum fun K hK => ?_
  rw [if_pos (hL K (Finset.mem_range.1 hK)), mul_one]
  obtain ⟨-, h2, -⟩ := win_eq i (n + K + 1) ω hω
  have e : (wsO i ω (n + K + 1)).2.2 = ω.1 (i, n + 1 + K) := by
    rw [show n + 1 + K = n + K + 1 by omega]; exact h2
  rw [e]

lemma depO_le {ω : CMT.Om M E} (hω : GoodO ω) {N0 : ℕ} {t : ℝ}
    (hc : Covers (FNO M) (arrO ω) N0 t) {j : Fin M × ℕ}
    (h : reqO ω j ≤ servedG (schO σ ω) j t) : depO σ j ω ≤ t := by
  refine csInf_le ⟨0, fun s hs => ?_⟩ h
  by_contra hneg
  have h0 := servedG_nonpos (schO σ ω) j (le_of_lt (lt_of_not_ge hneg))
  have : reqO ω j ≤ 0 := by simpa [h0] using (show reqO ω j ≤ servedG (schO σ ω) j s from hs)
  exact absurd this (not_le.2 (hω.2.1 j))

/-- V1: the response time of job `(i, n)` is at most the busy-period majorant after window `n`. -/
theorem resp_le_Bnd {ω : CMT.Om M E} (hω : GoodO ω) (n : ℕ) :
    ENNReal.ofReal (respO σ (i, n) ω) ≤ CMU.Bnd (wsO i ω) n := by
  classical
  by_cases hex : ∃ K, CMU.Xb (wsO i ω) n + CMU.Sy (wsO i ω) n K < 0
  · have hKs := Nat.find_spec hex
    set K := Nat.find hex with hKd
    have hK0 : 0 < K := by
      by_contra h0
      have hK : K = 0 := by omega
      rw [hK] at hKs
      have : CMU.Sy (wsO i ω) n 0 = 0 := by simp [CMU.Sy]
      linarith [Xb_nonneg i hω n]
    obtain ⟨N, hc⟩ := covers_of_good hω (arrO ω (i, n + K))
    obtain ⟨t, ht1, ht2, ht0⟩ := empties i hω hK0 hc hKs
    have hct : Covers (FNO M) (arrO ω) N t := covers_mono hc le_rfl ht2
    have hle : Wl (Le (keyO σ) (FNO M) N (i, n)) (arrO ω) (reqO ω) t = 0 := by
      apply le_antisymm _ (Wl_nonneg _ _ _ _)
      rw [← ht0]
      exact Wl_mono (Finset.filter_subset _ _) (fun l _ => (hω.2.1 l).le) t
    have hdone := done_of σ hω hct ht1 hle
    have hdep := depO_le σ hω hct hdone
    refine le_trans ?_ (Bnd_ge i hω n K fun K' hK' => le_of_not_gt (Nat.find_min hex hK'))
    apply ENNReal.ofReal_le_ofReal
    unfold respO
    linarith
  · simp only [not_exists, not_lt] at hex
    obtain ⟨N0, hN0⟩ := hω.2.2 (depO σ (i, n) ω)
    have hgt : depO σ (i, n) ω < arrO ω (i, n + N0) := by
      by_contra h
      have := hN0 (i, n + N0) (le_of_not_gt h)
      simp only at this
      omega
    refine le_trans ?_ (Bnd_ge i hω n N0 fun K _ => hex K)
    apply ENNReal.ofReal_le_ofReal
    unfold respO
    linarith

end CMV


/-! P3d (Mathlib part) for e14b429d: measurability of the response times, completion and
nonnegativity a.s., and the assembly on `CMT.PO`: integrable response times whose means converge.
Needs D1 (CMQ), P2a (CMR), P2b (CMT), P4 (CMU), P3, P3b, P3c (CMV). -/

set_option autoImplicit false

open MeasureTheory Set Finset Filter ProbabilityTheory

namespace CMV
open CMQ

variable {M : ℕ} {E : Type*} (σ : Equiv.Perm (Fin M)) (i : Fin M)

/-- the set of times at which job `j` is finished. -/
def doneSet (j : Fin M × ℕ) (ω : CMT.Om M E) : Set ℝ := {t : ℝ | reqO ω j ≤ servedG (schO σ ω) j t}

lemma depO_eq (j : Fin M × ℕ) (ω : CMT.Om M E) : depO σ j ω = sInf (doneSet σ j ω) := rfl

lemma doneSet_up (j : Fin M × ℕ) (ω : CMT.Om M E) {s t : ℝ} (h : s ≤ t) (hs : s ∈ doneSet σ j ω) :
    t ∈ doneSet σ j ω :=
  le_trans hs (servedG_mono _ _ h)

/-- completion: a finite majorant forces job `(i, n)` to finish. -/
lemma exists_done {ω : CMT.Om M E} (hω : GoodO ω) (n : ℕ) (hB : CMU.Bnd (wsO i ω) n < ⊤) :
    ∃ t, reqO ω (i, n) ≤ servedG (schO σ ω) (i, n) t := by
  classical
  by_cases hex : ∃ K, CMU.Xb (wsO i ω) n + CMU.Sy (wsO i ω) n K < 0
  · have hKs := Nat.find_spec hex
    set K := Nat.find hex with hKd
    have hK0 : 0 < K := by
      by_contra h0
      have hK : K = 0 := by omega
      rw [hK] at hKs
      have : CMU.Sy (wsO i ω) n 0 = 0 := by simp [CMU.Sy]
      linarith [Xb_nonneg i hω n]
    obtain ⟨N, hc⟩ := covers_of_good hω (arrO ω (i, n + K))
    obtain ⟨t, ht1, ht2, ht0⟩ := empties i hω hK0 hc hKs
    have hct : Covers (FNO M) (arrO ω) N t := covers_mono hc le_rfl ht2
    have hle : Wl (Le (keyO σ) (FNO M) N (i, n)) (arrO ω) (reqO ω) t = 0 := by
      apply le_antisymm _ (Wl_nonneg _ _ _ _)
      rw [← ht0]
      exact Wl_mono (Finset.filter_subset _ _) (fun l _ => (hω.2.1 l).le) t
    exact ⟨t, done_of σ hω hct ht1 hle⟩
  · exfalso
    simp only [not_exists, not_lt] at hex
    obtain ⟨N0, hN0⟩ := hω.2.2 ((CMU.Bnd (wsO i ω) n).toReal + arrO ω (i, n))
    have hgt : (CMU.Bnd (wsO i ω) n).toReal + arrO ω (i, n) < arrO ω (i, n + N0) := by
      by_contra h
      have := hN0 (i, n + N0) (le_of_not_gt h)
      simp only at this
      omega
    have h1 := Bnd_ge i hω n N0 fun K _ => hex K
    have h0 : 0 ≤ (CMU.Bnd (wsO i ω) n).toReal := ENNReal.toReal_nonneg
    have h2 : CMU.Bnd (wsO i ω) n < ENNReal.ofReal (arrO ω (i, n + N0) - arrO ω (i, n)) := by
      rw [← ENNReal.ofReal_toReal hB.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    exact absurd h1 (not_le.2 h2)

lemma resp_nonneg {ω : CMT.Om M E} (hω : GoodO ω) {j : Fin M × ℕ}
    (h : ∃ t, reqO ω j ≤ servedG (schO σ ω) j t) : 0 ≤ respO σ j ω := by
  unfold respO depO
  rw [sub_nonneg]
  refine le_csInf h fun t ht => ?_
  obtain ⟨N0, hc⟩ := covers_of_good hω t
  exact (done_imp σ hω hc ht).1.le

/-! ### measurability -/

section Meas
variable [MeasurableSpace E]

lemma measurable_arrO (l : Fin M × ℕ) : Measurable (fun ω : CMT.Om M E => arrO ω l) := by
  unfold arrO
  exact Finset.measurable_sum _ fun m _ => (measurable_pi_apply _).comp measurable_fst

lemma measurable_reqO (l : Fin M × ℕ) : Measurable (fun ω : CMT.Om M E => reqO ω l) :=
  (measurable_pi_apply l).comp (measurable_fst.comp measurable_snd)

lemma measurable_servedO (j : Fin M × ℕ) (q : ℝ) :
    Measurable (fun ω : CMT.Om M E => servedG (schO σ ω) j q) := by
  have hG := measurableSet_Sch (fun ω : CMT.Om M E => arrO ω) (fun ω => reqO ω) (keyO σ) (FNO M)
    (keyO_inj σ) j measurable_arrO measurable_reqO
  have h := measurable_measure_prodMk_left (ν := volume.restrict (Ico (0 : ℝ) q)) hG
  have e : (fun ω : CMT.Om M E => servedG (schO σ ω) j q) = fun ω =>
      ((volume.restrict (Ico (0 : ℝ) q)) (Prod.mk ω ⁻¹'
        {p : CMT.Om M E × ℝ | Sch (keyO σ) (FNO M) (arrO p.1) (reqO p.1) p.2 = some j})).toReal := by
    funext ω
    rw [Measure.restrict_apply (measurable_prodMk_left hG)]
    rfl
  rw [e]
  exact h.ennreal_toReal

lemma measurable_depO (j : Fin M × ℕ) : Measurable (depO σ j : CMT.Om M E → ℝ) := by
  have hS : ∀ q : ℝ, MeasurableSet {ω : CMT.Om M E | q ∈ doneSet σ j ω} := fun q =>
    measurableSet_le (measurable_reqO j) (measurable_servedO σ j q)
  refine measurable_of_Iio fun c => ?_
  have e : depO σ j ⁻¹' Iio c =
      ({ω : CMT.Om M E | reqO ω j ≤ 0} ∩ {_ω | 0 < c}) ∪
      ({ω | 0 < reqO ω j} ∩ ((⋃ q : ℚ, {_ω : CMT.Om M E | (q : ℝ) < c} ∩
          {ω | (q : ℝ) ∈ doneSet σ j ω}) ∪
        ((⋂ q : ℚ, {ω | (q : ℝ) ∈ doneSet σ j ω}ᶜ) ∩ {_ω | 0 < c}))) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff]
    rw [depO_eq]
    by_cases hr : 0 < reqO ω j
    · have hb : BddBelow (doneSet σ j ω) := ⟨0, fun s hs => by
        by_contra h
        have h0 := servedG_nonpos (schO σ ω) j (le_of_lt (lt_of_not_ge h))
        have hs' : reqO ω j ≤ servedG (schO σ ω) j s := hs
        linarith⟩
      by_cases hne : (doneSet σ j ω).Nonempty
      · have hq : ¬ ∀ q : ℚ, (q : ℝ) ∉ doneSet σ j ω := by
          obtain ⟨s, hs⟩ := hne
          obtain ⟨q, hq⟩ := exists_rat_gt s
          exact fun h => h q (doneSet_up σ j ω hq.le hs)
        constructor
        · intro hlt
          obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne hlt
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsc
          exact Or.inr ⟨hr, Or.inl ⟨q, hq2, doneSet_up σ j ω hq1.le hs⟩⟩
        · rintro (⟨h1, _⟩ | ⟨_, (⟨q, hq1, hq2⟩ | ⟨h, _⟩)⟩)
          · linarith
          · exact lt_of_le_of_lt (csInf_le hb hq2) hq1
          · exact absurd h hq
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Real.sInf_empty]
        constructor
        · intro hc
          exact Or.inr ⟨hr, Or.inr ⟨fun q hq => Set.notMem_empty _ hq, hc⟩⟩
        · rintro (⟨h1, _⟩ | ⟨_, (⟨q, _, hq2⟩ | ⟨_, hc⟩)⟩)
          · linarith
          · exact absurd hq2 (Set.notMem_empty _)
          · exact hc
    · have huniv : doneSet σ j ω = Set.univ := by
        ext t
        simp only [doneSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (not_lt.1 hr) ENNReal.toReal_nonneg
      rw [huniv, Real.sInf_of_not_bddBelow not_bddBelow_univ]
      constructor
      · intro hc
        exact Or.inl ⟨not_lt.1 hr, hc⟩
      · rintro (⟨_, hc⟩ | ⟨h1, _⟩)
        · exact hc
        · exact absurd h1 hr
  rw [e]
  refine ((measurableSet_le (measurable_reqO j) measurable_const).inter
    (MeasurableSet.const _)).union ((measurableSet_lt measurable_const (measurable_reqO j)).inter
      ((MeasurableSet.iUnion fun q : ℚ => (MeasurableSet.const _).inter (hS (q : ℝ))).union
        ((MeasurableSet.iInter fun q : ℚ => (hS (q : ℝ)).compl).inter (MeasurableSet.const _))))

lemma measurable_respO (j : Fin M × ℕ) : Measurable (respO σ j : CMT.Om M E → ℝ) :=
  (measurable_depO σ j).sub (measurable_arrO j)

lemma measurable_Sy (k L : ℕ) : Measurable (fun ws : ℕ → ℝ × ℝ × ℝ => CMU.Sy ws k L) := by
  unfold CMU.Sy
  refine Finset.measurable_sum _ fun l _ => ?_
  have h := measurable_pi_apply (X := fun _ : ℕ => ℝ × ℝ × ℝ) (k + 1 + l)
  exact (h.fst.add h.snd.fst).sub h.snd.snd

lemma measurable_Xb (n : ℕ) : Measurable (fun ws : ℕ → ℝ × ℝ × ℝ => CMU.Xb ws n) := by
  have e : (fun ws : ℕ → ℝ × ℝ × ℝ => CMU.Xb ws n) =
      (range (n + 1)).sup' nonempty_range_add_one
        (fun k (ws : ℕ → ℝ × ℝ × ℝ) => (ws k).1 + (ws k).2.1 + CMU.Sy ws k (n - k)) := by
    funext ws
    rw [Finset.sup'_apply]
    rfl
  rw [e]
  refine Finset.measurable_sup' _ fun k _ => ?_
  have h := measurable_pi_apply (X := fun _ : ℕ => ℝ × ℝ × ℝ) k
  exact (h.fst.add h.snd.fst).add (measurable_Sy k (n - k))

lemma measurable_Bnd (n : ℕ) : Measurable (fun ws : ℕ → ℝ × ℝ × ℝ => CMU.Bnd ws n) := by
  unfold CMU.Bnd
  refine Measurable.ennreal_tsum fun K => ?_
  have h := measurable_pi_apply (X := fun _ : ℕ => ℝ × ℝ × ℝ) (n + K + 1)
  exact (ENNReal.measurable_ofReal.comp h.snd.snd).mul (Measurable.ite
    (measurableSet_le measurable_const ((measurable_Xb n).add (measurable_Sy n K)))
    measurable_const measurable_const)

lemma measurable_orbit : Measurable (fun (ω : CMT.Om M E) (m : ℕ) => wsO i ω m) :=
  measurable_pi_lambda _ fun m => (CMT.measurable_WinO i).comp ((CMT.measurable_thO i).iterate m)

end Meas

/-! ### assembly on the multi-class law -/

section Assembly
variable [MeasurableSpace E] (lam mu : Fin M → ℝ)
  [∀ k, IsProbabilityMeasure (expMeasure (lam k))] [∀ k, IsProbabilityMeasure (expMeasure (mu k))]
  (η : Measure E) [IsProbabilityMeasure η]

/-- **P3 assembly.** Under the load condition, for the static priority order `σ`, every response
time of class `i` is integrable and the means converge. -/
theorem achieves_O (hlam : ∀ k, 0 < lam k) (hmu : ∀ k, 0 < mu k) (hρ : ∑ k, lam k / mu k < 1)
    (hgood : ∀ᵐ ω ∂(CMT.PO (fun k => expMeasure (lam k)) (fun k => expMeasure (mu k)) η), GoodO ω) :
    (∀ n, Integrable (respO σ (i, n))
      (CMT.PO (fun k => expMeasure (lam k)) (fun k => expMeasure (mu k)) η)) ∧
    ∃ W : ℝ, Tendsto (fun n => ∫ ω, respO σ (i, n) ω
      ∂(CMT.PO (fun k => expMeasure (lam k)) (fun k => expMeasure (mu k)) η)) atTop (nhds W) := by
  set P := CMT.PO (fun k => expMeasure (lam k)) (fun k => expMeasure (mu k)) η with hP
  obtain ⟨C, hC, hCb⟩ := CMU.Bnd_bounded lam mu η hlam hmu i hρ
  have hzeta : P.map (CMT.WinO i) = CMU.zeta lam mu η i := by
    rw [show (CMT.WinO (M := M) (E := E) i) = CMT.WinS i ∘ CMT.toS from rfl,
      ← Measure.map_map (CMT.measurable_WinS i) CMT.measurable_toS,
      show P.map CMT.toS = _ from CMT.map_toS' lam (fun k => expMeasure (mu k)) η]
  have hB : ∀ n, ∫⁻ ω, CMU.Bnd (wsO i ω) n ∂P ≤ C := by
    intro n
    have h1 : ∫⁻ ω, CMU.Bnd (wsO i ω) n ∂P =
        ∫⁻ ws, CMU.Bnd ws n ∂(P.map fun ω m => wsO i ω m) :=
      (lintegral_map (measurable_Bnd n) (measurable_orbit i)).symm
    rw [h1]
    have h2 := CMT.map_windows_iid lam (fun k => expMeasure (mu k)) η hlam i
    have key : ∀ (ν : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure ν], ν = CMU.zeta lam mu η i →
        ∫⁻ ws, CMU.Bnd ws n ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ C := by
      intro ν _ hν
      subst hν
      exact hCb n
    haveI : IsProbabilityMeasure (P.map (CMT.WinO i)) :=
      Measure.isProbabilityMeasure_map (CMT.measurable_WinO i).aemeasurable
    have h3 : (P.map fun ω m => wsO i ω m) = Measure.infinitePi fun _ : ℕ => P.map (CMT.WinO i) :=
      h2
    rw [h3]
    exact key _ hzeta
  have hresp : ∀ n, ∫⁻ ω, ENNReal.ofReal (respO σ (i, n) ω) ∂P ≤ C := fun n =>
    le_trans (lintegral_mono_ae (hgood.mono fun ω hω => resp_le_Bnd σ i hω n)) (hB n)
  have hdone : ∀ n, ∀ᵐ ω ∂P, ∃ t, reqO ω (i, n) ≤ servedG (schO σ ω) (i, n) t := by
    intro n
    have hfin := ae_lt_top' ((measurable_Bnd n).comp (measurable_orbit i)).aemeasurable
      (ne_top_of_le_ne_top hC.ne (hB n))
    filter_upwards [hgood, hfin] with ω hω hf
    exact exists_done σ i hω n hf
  have hnn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ respO σ (i, n) ω := fun n => by
    filter_upwards [hgood, hdone n] with ω hω hd
    exact resp_nonneg σ hω hd
  have hint : ∀ n, Integrable (respO σ (i, n)) P := fun n =>
    ⟨(measurable_respO σ (i, n)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (hnn n)).2 (lt_of_le_of_lt (hresp n) hC)⟩
  refine ⟨hint, ?_⟩
  have hmono : Monotone fun n => ∫ ω, respO σ (i, n) ω ∂P := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hmap : P.map (CMT.thO i) = P := CMT.map_thO lam (fun k => expMeasure (mu k)) η hlam i
    have hi1 : Integrable (respO σ (i, n)) (P.map (CMT.thO i)) := by
      rw [hmap]; exact hint n
    have hi2 : Integrable (fun ω => respO σ (i, n) (CMT.thO i ω)) P :=
      hi1.comp_measurable (CMT.measurable_thO i)
    have e : ∫ ω, respO σ (i, n) ω ∂P = ∫ ω, respO σ (i, n) (CMT.thO i ω) ∂P := by
      conv_lhs => rw [← hmap]
      exact integral_map (CMT.measurable_thO i).aemeasurable
        (measurable_respO σ (i, n)).aestronglyMeasurable
    show ∫ ω, respO σ (i, n) ω ∂P ≤ ∫ ω, respO σ (i, n + 1) ω ∂P
    rw [e]
    refine integral_mono_ae hi2 (hint (n + 1)) ?_
    filter_upwards [hgood, hdone (n + 1)] with ω hω hd
    exact resp_thO_le σ i hω n hd
  have hbdd : BddAbove (Set.range fun n => ∫ ω, respO σ (i, n) ω ∂P) := by
    refine ⟨C.toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    show ∫ ω, respO σ (i, n) ω ∂P ≤ C.toReal
    rw [integral_eq_lintegral_of_nonneg_ae (hnn n) (measurable_respO σ (i, n)).aestronglyMeasurable]
    exact ENNReal.toReal_mono hC.ne (hresp n)
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

end Assembly

end CMV


/-! ## P1b: almost surely, arrival epochs of every class are unbounded (Covers a.s.) -/

namespace CMP
open CoffmanMitrani MeasureTheory ProbabilityTheory Filter Finset

/-- clipping to `[0,1]`. -/
noncomputable def clip (y : ℝ) : ℝ := min (max y 0) 1

lemma measurable_clip : Measurable clip := by
  unfold clip; fun_prop

lemma clip_nonneg (y : ℝ) : 0 ≤ clip y := by
  unfold clip; exact le_min (le_max_right _ _) zero_le_one

lemma clip_le_one (y : ℝ) : clip y ≤ 1 := min_le_right _ _

lemma clip_pos {y : ℝ} (hy : 0 < y) : 0 < clip y := by
  unfold clip; rw [max_eq_left hy.le]; exact lt_min hy one_pos

lemma clip_le {y : ℝ} (hy : 0 ≤ y) : clip y ≤ y := by
  unfold clip; rw [max_eq_left hy]; exact min_le_left _ _

/-- partial sums of iid a.s. positive variables are unbounded a.s. (SLLN on the clipped variables). -/
theorem ae_unbounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (Y n)) (hind : iIndepFun Y μ)
    (hid : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) (hpos : ∀ᵐ ω ∂μ, 0 < Y 0 ω) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (Y m ω) := by
  set X : ℕ → Ω → ℝ := fun n ω => clip (Y n ω) with hX
  have hindX : iIndepFun X μ := hind.comp (fun _ => clip) (fun _ => measurable_clip)
  have hidX : ∀ n, IdentDistrib (X n) (X 0) μ μ := fun n => (hid n).comp measurable_clip
  have hmX : Measurable (X 0) := measurable_clip.comp (hmeas 0)
  have hint : Integrable (X 0) μ := by
    refine Integrable.of_bound hmX.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (clip_nonneg _)]
    exact clip_le_one _
  have hc : 0 < μ[X 0] := by
    rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun ω => clip_nonneg _) hint]
    have hs : ∀ᵐ ω ∂μ, ω ∈ Function.support (X 0) := hpos.mono fun ω h => (clip_pos h).ne'
    rw [pos_iff_ne_zero]
    intro h0
    have h1 : μ (Function.support (X 0))ᶜ = 0 := by
      rw [ae_iff] at hs; simpa [Set.compl_def] using hs
    have : μ Set.univ ≤ 0 := by
      calc μ Set.univ = μ (Function.support (X 0) ∪ (Function.support (X 0))ᶜ) := by
            rw [Set.union_compl_self]
        _ ≤ μ (Function.support (X 0)) + μ (Function.support (X 0))ᶜ := measure_union_le _ _
        _ = 0 := by rw [h0, h1, add_zero]
    simp at this
  have hslln := strong_law_ae_real X hint (fun i j hij => hindX.indepFun hij) hidX
  filter_upwards [hslln] with ω hω
  intro T
  set c := μ[X 0]
  have e1 := (tendsto_order.1 hω).1 (c / 2) (half_lt_self hc)
  have e2 : ∀ᶠ n : ℕ in atTop, T * 2 / c < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  have e3 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨n, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  refine ⟨n, ?_⟩
  have h4 : c / 2 * n < ∑ i ∈ range n, X i ω := by rwa [lt_div_iff₀ h3] at h1
  have h5 : T < c / 2 * n := by
    have := mul_lt_mul_of_pos_left h2 (half_pos hc)
    have he : c / 2 * (T * 2 / c) = T := by field_simp
    linarith
  exact lt_trans h5 h4

lemma ae_pos_expMeasure (r : ℝ) : ∀ᵐ y ∂(expMeasure r), 0 < y := by
  rw [ae_iff]
  simp only [not_lt]
  unfold expMeasure gammaMeasure
  show (volume.withDensity (gammaPDF 1 r)) (Set.Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- one class's interarrival stream inside the product of exponentials. -/
theorem ae_unbounded_infinitePi {M : ℕ} (rate : Fin M → ℝ) (hrate : ∀ i, 0 < rate i) :
    haveI : ∀ j : Job M, IsProbabilityMeasure (expMeasure (rate j.1)) :=
      fun j => isProbabilityMeasure_expMeasure (hrate j.1)
    ∀ᵐ x ∂(Measure.infinitePi (fun j : Job M => expMeasure (rate j.1))),
      (∀ j, 0 < x j) ∧ ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m)) := by
  haveI : ∀ j : Job M, IsProbabilityMeasure (expMeasure (rate j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (hrate j.1)
  set μ0 := Measure.infinitePi (fun j : Job M => expMeasure (rate j.1))
  have hpos : ∀ᵐ x ∂μ0, ∀ j, 0 < x j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi _ j).quasiMeasurePreserving.ae (ae_pos_expMeasure _)
  have hall : ∀ᵐ x ∂μ0, ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m)) := by
    rw [ae_all_iff]
    intro k
    have hind0 : iIndepFun (fun (j : Job M) (x : Job M → ℝ) => x j) μ0 :=
      iIndepFun_infinitePi (X := fun _ y => y) (fun _ => measurable_id)
    have hind : iIndepFun (fun (n : ℕ) (x : Job M → ℝ) => x (k, n)) μ0 :=
      hind0.precomp (g := fun n : ℕ => (k, n)) (fun a b h => by simpa using h)
    refine ae_unbounded (fun n (x : Job M → ℝ) => x (k, n)) (fun n => measurable_pi_apply _)
      hind (fun n => ?_) ?_
    · refine ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable, ?_⟩
      rw [(measurePreserving_eval_infinitePi _ (k, n)).map_eq,
        (measurePreserving_eval_infinitePi _ (k, 0)).map_eq]
    · exact (measurePreserving_eval_infinitePi _ (k, 0)).quasiMeasurePreserving.ae
        (ae_pos_expMeasure _)
  filter_upwards [hpos, hall] with x h1 h2
  exact ⟨h1, h2⟩

/-- deterministic step: unbounded clipped partial sums give a finite cover of `{l | arrival ≤ T}`. -/
lemma covers_of {M : ℕ} (x : Job M → ℝ) (hpos : ∀ j, 0 < x j)
    (hu : ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m))) :
    ∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job M, (∑ m ∈ range (l.2 + 1), x (l.1, m)) ≤ T → l.2 < N0 := by
  intro T
  choose n hn using fun k => hu k T
  refine ⟨∑ k, n k, fun l hl => ?_⟩
  by_contra hge
  push_neg at hge
  have hk : n l.1 ≤ l.2 :=
    le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ l.1)) hge
  have a1 : ∑ m ∈ range (n l.1), clip (x (l.1, m)) ≤ ∑ m ∈ range (n l.1), x (l.1, m) :=
    Finset.sum_le_sum fun m _ => clip_le (hpos _).le
  have a2 : ∑ m ∈ range (n l.1), x (l.1, m) ≤ ∑ m ∈ range (l.2 + 1), x (l.1, m) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun m _ _ => (hpos _).le
  linarith [hn l.1]

/-- P1b on the platform space: a.s. positive interarrivals and every window `(-∞, T]` holds
finitely many arrivals, all of index below some `N0`. -/
theorem ae_covers (D : Data) :
    ∀ᵐ ω ∂D.P, (∀ j, 0 < ω.1 j) ∧
      ∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job D.M, arrival ω l ≤ T → l.2 < N0 := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have h1 := ae_unbounded_infinitePi D.lam D.lam_pos
  unfold Data.P
  have g1 := (Measure.quasiMeasurePreserving_fst (μ := Measure.infinitePi
    fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
      fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
        fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae h1
  filter_upwards [g1] with ω ⟨hp, hu⟩
  exact ⟨hp, fun T => covers_of ω.1 hp hu T⟩

end CMP

/-! ## Bridge to the platform definitions (casefs compile only) -/

namespace CMB
open CoffmanMitrani CMQ MeasureTheory

variable {M : ℕ}

/-- priority key: class rank under `σ`, then index (FCFS within a class). -/
def key (σ : Equiv.Perm (Fin M)) (j : Job M) : Lex (Fin M × ℕ) := toLex (σ.symm j.1, j.2)

lemma key_inj (σ : Equiv.Perm (Fin M)) : Function.Injective (key σ) := by
  intro j j' h
  unfold key at h
  have h2 := toLex.injective h
  simp only [Prod.mk.injEq] at h2
  exact Prod.ext (σ.symm.injective h2.1) h2.2

def FN (M : ℕ) (N : ℕ) : Finset (Job M) := Finset.univ ×ˢ Finset.range N

lemma FN_mono (M : ℕ) : Monotone (FN M) := by
  intro N N' h j hj
  simp only [FN, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hj ⊢
  omega

/-- the static preemptive priority schedule. -/
noncomputable def schedule (σ : Equiv.Perm (Fin M)) : Schedule M :=
  fun ω t => Sch (key σ) (FN M) (arrival ω) (serviceReq ω) t

def Good (ω : Omega M) : Prop :=
  (∀ j, 0 ≤ arrival ω j) ∧ (∀ j, 0 < serviceReq ω j) ∧
    ∀ T, ∃ N0, Covers (FN M) (arrival ω) N0 T

variable (σ : Equiv.Perm (Fin M)) {ω : Omega M}

lemma served_eq_servedG (j : Job M) (t : ℝ) :
    served (schedule σ) j ω t = servedG (Sch (key σ) (FN M) (arrival ω) (serviceReq ω)) j t := rfl

theorem good_prio (hω : Good ω) (t : ℝ) (j j' : Job M) (hS : schedule σ ω t = some j)
    (hp : present (schedule σ) j' ω t) :
    σ.symm j.1 < σ.symm j'.1 ∨ (j.1 = j'.1 ∧ j.2 ≤ j'.2) := by
  obtain ⟨ha, hr, hcov⟩ := hω
  have := sched_prio (key_inj σ) (FN_mono M) ha hr (hcov t) hS hp.1 hp.2
  unfold key at this
  rw [Prod.Lex.toLex_le_toLex] at this
  rcases this with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨σ.symm.injective h1, h2⟩

theorem good_cl2 (hω : Good ω) (t : ℝ) (j : Job M) (hS : schedule σ ω t = some j) :
    present (schedule σ) j ω t := by
  obtain ⟨ha, hr, hcov⟩ := hω
  exact sched_present (key_inj σ) (FN_mono M) ha hr (hcov t) hS

theorem good_cl3 (hω : Good ω) (t : ℝ) :
    schedule σ ω t = none ↔ ∀ j : Job M, ¬ present (schedule σ) j ω t := by
  constructor
  · intro hS j hp
    obtain ⟨ha, hr, hcov⟩ := hω
    have := sched_none (key_inj σ) (FN_mono M) ha hr (hcov t) hS hp.1
    exact absurd hp.2 (not_lt.2 this)
  · intro h
    cases hS : schedule σ ω t with
    | none => rfl
    | some j => exact absurd (good_cl2 σ hω t j hS) (h j)

theorem isPriority_of_ae_good (D : Data) (σ : Equiv.Perm (Fin D.M))
    (h : ∀ᵐ ω ∂D.P, Good ω) : IsPriority D σ (schedule σ) := by
  unfold IsPriority
  filter_upwards [h] with ω hω
  intro t j j' hS hp
  exact good_prio σ hω t j j' hS hp

end CMB

/-! ## Bridge part 2: clause 5 (the history rule) -/

namespace CMB
open CoffmanMitrani CMQ MeasureTheory

variable {M : ℕ}

/-- visible and present in a history: arrived and not yet departed. -/
def Vis (h : History M) (p : Fin M × ℕ) : Prop := h.arrivals p ≠ none ∧ h.departures p = none

open Classical in
/-- the static-priority rule: least key among visible present jobs. -/
noncomputable def rule (σ : Equiv.Perm (Fin M)) (h : History M) (_ : ℕ → unitInterval) :
    Option (Fin M × ℕ) :=
  if hx : ∃ p, Vis h p ∧ ∀ q, Vis h q → key σ p ≤ key σ q then some hx.choose else none

variable (σ : Equiv.Perm (Fin M)) {ω : Omega M}

lemma arrival_strictMono (hpos : ∀ j, 0 < ω.1 j) (k : Fin M) :
    StrictMono (fun m : ℕ => arrival ω (k, m)) := by
  apply strictMono_nat_of_lt_succ
  intro m
  simp only [arrival]
  rw [Finset.sum_range_succ _ (m + 1)]
  linarith [hpos (k, m + 1)]

/-- `classOffset` counts exactly the indices arriving before `a0`. -/
lemma lt_offset_iff (hω : Good ω) (hpos : ∀ j, 0 < ω.1 j) (j0 : Job M) (k : Fin M) (m : ℕ) :
    m < classOffset ω j0 k ↔ arrival ω (k, m) < arrival ω j0 := by
  classical
  obtain ⟨_, _, hcov⟩ := hω
  obtain ⟨N0, hc⟩ := hcov (arrival ω j0)
  have hex : ∃ n, arrival ω j0 ≤ arrival ω (k, n) := by
    refine ⟨N0, ?_⟩
    by_contra hcon
    push_neg at hcon
    have := hc (k, N0) (le_of_lt hcon)
    simp [FN] at this
  have hmono := arrival_strictMono hpos k
  have hset : {m : ℕ | arrival ω (k, m) < arrival ω j0} = ↑(Finset.range (Nat.find hex)) := by
    ext m
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro hm
      by_contra hcon
      push_neg at hcon
      have := hmono.monotone hcon
      have := Nat.find_spec hex
      linarith
    · intro hm
      have := Nat.find_min hex hm
      push_neg at this
      exact this
  have hoff : classOffset ω j0 k = Nat.find hex := by
    unfold classOffset
    rw [hset, Set.ncard_coe_finset, Finset.card_range]
  rw [hoff, ← Finset.mem_range, ← Finset.mem_coe, ← hset]
  rfl

lemma workIn_ge (hω : Good ω) (G : Finset (Job M)) (x b : ℝ) :
    Ain G (arrival ω) (serviceReq ω) x b ≤ workIn ω x b := by
  classical
  obtain ⟨_, hr, hcov⟩ := hω
  obtain ⟨N0, hc⟩ := hcov b
  have hnn : ∀ j, 0 ≤ Set.indicator {j : Job M | x ≤ arrival ω j ∧ arrival ω j < b}
      (serviceReq ω) j := fun j => Set.indicator_nonneg (fun j _ => le_of_lt (hr j)) j
  have hsum : Summable (fun j => Set.indicator {j : Job M | x ≤ arrival ω j ∧ arrival ω j < b}
      (serviceReq ω) j) := by
    apply summable_of_ne_finset_zero (s := FN M N0)
    intro j hj
    apply Set.indicator_of_notMem
    rintro ⟨_, h2⟩
    exact hj (hc j (le_of_lt h2))
  unfold workIn Ain
  calc ∑ l ∈ G.filter (fun l => x ≤ arrival ω l ∧ arrival ω l < b), serviceReq ω l
      = ∑ l ∈ G, Set.indicator {j : Job M | x ≤ arrival ω j ∧ arrival ω j < b}
          (serviceReq ω) l := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro l _
        simp only [Set.indicator, Set.mem_setOf_eq]
    _ ≤ _ := hsum.sum_le_tsum G (fun j _ => hnn j)

/-- at a busy-period start nothing older than `j0` is present at any later time. -/
lemma old_not_present (hω : Good ω) (hpos : ∀ j, 0 < ω.1 j) {j0 : Job M}
    (hbp : IsBPStart ω j0) {t : ℝ} (ht : arrival ω j0 ≤ t) {j : Job M}
    (hp : present (schedule σ) j ω t) : classOffset ω j0 j.1 ≤ j.2 := by
  by_contra hcon
  push_neg at hcon
  have hlt := (lt_offset_iff hω hpos j0 j.1 j.2).1 hcon
  obtain ⟨ha, hr, hcov⟩ := hω
  have := sched_bp (key_inj σ) (FN_mono M) ha hr (hcov (arrival ω j0))
    (fun G x hx => le_trans (workIn_ge ⟨ha, hr, hcov⟩ G x _) (hbp x hx)) hlt ht
  exact absurd hp.2 (not_lt.2 this)

lemma key_shift_le {off : Fin M → ℕ} {p q : Fin M × ℕ} :
    key σ (p.1, off p.1 + p.2) ≤ key σ (q.1, off q.1 + q.2) ↔ key σ p ≤ key σ q := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      have : p.1 = q.1 := σ.symm.injective h1
      simp only at h2
      rw [this] at h2
      omega
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      have : p.1 = q.1 := σ.symm.injective h1
      simp only
      rw [this]
      omega

/-- clause 5 pathwise. -/
theorem good_cl5 (hω : Good ω) (hpos : ∀ j, 0 < ω.1 j) (j0 : Job M) (t : ℝ)
    (hbp : IsBPStart ω j0) (hin : InBP ω j0 t) :
    schedule σ ω t = (rule σ (history (schedule σ) ω j0 t) (seed ω j0)).map
      (fun p => (p.1, classOffset ω j0 p.1 + p.2)) := by
  classical
  set off := classOffset ω j0 with hoff
  set h := history (schedule σ) ω j0 t with hh
  have hvis : ∀ p, Vis h p ↔ present (schedule σ) (p.1, off p.1 + p.2) ω t := by
    intro p
    simp only [Vis, hh, history, present, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false,
      not_not, not_le]
    simp only [hoff, not_lt]
  have ht : arrival ω j0 ≤ t := hin.1
  cases hS : schedule σ ω t with
  | none =>
    have hnp := (good_cl3 σ hω t).1 hS
    unfold rule
    rw [dif_neg]
    · rfl
    · rintro ⟨p, hp, _⟩
      exact hnp _ ((hvis p).1 hp)
  | some j =>
    have hpj := good_cl2 σ hω t j hS
    have hoffj := old_not_present σ hω hpos hbp ht hpj
    rw [← hoff] at hoffj
    set p0 : Fin M × ℕ := (j.1, j.2 - off j.1) with hp0
    have hfp0 : (p0.1, off p0.1 + p0.2) = j := by
      simp only [hp0]; ext <;> simp; omega
    have hmin : ∀ q, Vis h q → key σ p0 ≤ key σ q := by
      intro q hq
      have hpq := (hvis q).1 hq
      obtain ⟨ha, hr, hcov⟩ := hω
      have := sched_prio (key_inj σ) (FN_mono M) ha hr (hcov t) hS hpq.1 hpq.2
      rw [← hfp0] at this
      exact (key_shift_le σ).1 this
    have hV0 : Vis h p0 := (hvis p0).2 (by rw [hfp0]; exact hpj)
    have hex : ∃ p, Vis h p ∧ ∀ q, Vis h q → key σ p ≤ key σ q := ⟨p0, hV0, hmin⟩
    unfold rule
    rw [dif_pos hex]
    have hc := hex.choose_spec
    have heq : hex.choose = p0 :=
      (key_inj σ) (le_antisymm (hc.2 p0 hV0) (hmin _ hc.1))
    simp only [Option.map_some]
    rw [heq, hfp0]

end CMB

/-! ## Bridge part 3: clause 1 and the IsStrategy assembly -/

namespace CMB
open CoffmanMitrani CMQ MeasureTheory

variable {M : ℕ}

lemma measurable_arrival (l : Job M) : Measurable (fun ω : Omega M => arrival ω l) := by
  unfold arrival
  apply Finset.measurable_sum
  intro m _
  exact (measurable_pi_apply _).comp measurable_fst

lemma measurable_serviceReq (l : Job M) : Measurable (fun ω : Omega M => serviceReq ω l) := by
  unfold serviceReq
  exact (measurable_pi_apply l).comp (measurable_fst.comp measurable_snd)

theorem measurableSet_schedule (σ : Equiv.Perm (Fin M)) (j : Job M) :
    MeasurableSet {p : Omega M × ℝ | schedule σ p.1 p.2 = some j} :=
  measurableSet_Sch (fun ω => arrival ω) (fun ω => serviceReq ω) (key σ) (FN M) (key_inj σ) j
    measurable_arrival measurable_serviceReq

/-- IsStrategy from the a.s. pathwise facts; clause 4 (completion) stays a hypothesis. -/
theorem isStrategy_of_ae (D : Data) (σ : Equiv.Perm (Fin D.M))
    (h : ∀ᵐ ω ∂D.P, Good ω ∧ (∀ j, 0 < ω.1 j) ∧
      ∀ j : Job D.M, ∃ t : ℝ, serviceReq ω j ≤ served (schedule σ) j ω t) :
    IsStrategy D (schedule σ) := by
  refine ⟨fun j => (measurableSet_schedule σ j).nullMeasurableSet, rule σ, ?_⟩
  filter_upwards [h] with ω ⟨hω, hpos, hdone⟩
  exact ⟨fun t j hS => good_cl2 σ hω t j hS, fun t => good_cl3 σ hω t, hdone,
    fun j0 t hbp hin => good_cl5 σ hω hpos j0 t hbp hin⟩

end CMB

/-! ## Bridge part 4 (P1a): a.s. positivity of all coordinates -/

namespace CMB
open CoffmanMitrani CMQ MeasureTheory ProbabilityTheory

lemma ae_pos_expMeasure (r : ℝ) : ∀ᵐ y ∂(expMeasure r), 0 < y := by
  rw [ae_iff]
  simp only [not_lt]
  unfold expMeasure gammaMeasure
  show (volume.withDensity (gammaPDF 1 r)) (Set.Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma ae_pos_infinitePi {ι : Type*} [Countable ι] (rate : ι → ℝ) (hrate : ∀ i, 0 < rate i) :
    haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
      fun i => isProbabilityMeasure_expMeasure (hrate i)
    ∀ᵐ x ∂(Measure.infinitePi (fun i => expMeasure (rate i))), ∀ i, 0 < x i := by
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval_infinitePi _ i).quasiMeasurePreserving.ae (ae_pos_expMeasure _)

theorem ae_pos (D : Data) :
    ∀ᵐ ω ∂D.P, (∀ j, 0 < ω.1 j) ∧ (∀ j, 0 < ω.2.1 j) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have h1 := ae_pos_infinitePi (fun j : Job D.M => D.lam j.1) (fun j => D.lam_pos j.1)
  have h2 := ae_pos_infinitePi (fun j : Job D.M => D.mu j.1) (fun j => D.mu_pos j.1)
  unfold Data.P
  have g1 := (Measure.quasiMeasurePreserving_fst (μ := Measure.infinitePi
    fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
      fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
        fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae h1
  have g2 := (Measure.quasiMeasurePreserving_snd (μ := Measure.infinitePi
    fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
      fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
        fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae
    ((Measure.quasiMeasurePreserving_fst).ae h2)
  filter_upwards [g1, g2] with ω h1 h2
  exact ⟨h1, h2⟩

lemma arrival_nonneg {M : ℕ} {ω : Omega M} (hpos : ∀ j, 0 < ω.1 j) (j : Job M) :
    0 ≤ arrival ω j :=
  Finset.sum_nonneg (fun m _ => le_of_lt (hpos _))

end CMB

/-! ## Bridge part 5 (P1b + P1c): Good a.s. and completion (IsStrategy clause 4) a.s. -/

namespace CMB
open CoffmanMitrani CMQ MeasureTheory ProbabilityTheory Filter Finset Topology

lemma Abef_FN_eq {M : ℕ} (ω : Omega M) (N0 : ℕ) (T : ℝ) :
    Abef (FN M N0) (arrival ω) (serviceReq ω) T =
      ∑ k, ∑ n ∈ (range N0).filter (fun n => ∑ m ∈ range (n + 1), ω.1 (k, m) < T),
        ω.2.1 (k, n) := by
  unfold Abef FN
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold arrival serviceReq
  split_ifs <;> rfl

theorem ae_facts (D : Data) :
    ∀ᵐ ω ∂D.P, (∀ j, 0 < ω.1 j) ∧ (∀ j, 0 < ω.2.1 j) ∧
      (∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job D.M, arrival ω l ≤ T → l.2 < N0) ∧
      (∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.1 (k, m)) / (n : ℝ)) atTop
        (𝓝 (1 / D.lam k))) ∧
      (∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.2.1 (k, m)) / (n : ℝ)) atTop
        (𝓝 (1 / D.mu k))) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hA := CMS.ae_slln_infinitePi D.lam D.lam_pos
  have hS := CMS.ae_slln_infinitePi D.mu D.mu_pos
  have g1 : ∀ᵐ ω ∂D.P, ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.1 (k, m)) / (n : ℝ))
      atTop (𝓝 (1 / D.lam k)) :=
    (Measure.quasiMeasurePreserving_fst (μ := Measure.infinitePi
      fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
        fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
          fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae hA
  have g2 : ∀ᵐ ω ∂D.P, ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.2.1 (k, m)) / (n : ℝ))
      atTop (𝓝 (1 / D.mu k)) :=
    (Measure.quasiMeasurePreserving_snd (μ := Measure.infinitePi
      fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
        fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
          fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae
      ((Measure.quasiMeasurePreserving_fst).ae hS)
  filter_upwards [ae_pos D, CMP.ae_covers D, g1, g2] with ω h1 h2 h3 h4
  exact ⟨h1.1, h1.2, h2.2, h3, h4⟩

theorem complete_of (D : Data) (σ : Equiv.Perm (Fin D.M)) {ω : Omega D.M}
    (hp1 : ∀ j, 0 < ω.1 j) (hp2 : ∀ j, 0 < ω.2.1 j)
    (hcov : ∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job D.M, arrival ω l ≤ T → l.2 < N0)
    (hx : ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.1 (k, m)) / (n : ℝ)) atTop
      (𝓝 (1 / D.lam k)))
    (hs : ∀ k, Tendsto (fun n : ℕ => (∑ m ∈ range n, ω.2.1 (k, m)) / (n : ℝ)) atTop
      (𝓝 (1 / D.mu k))) (j : Job D.M) :
    ∃ t : ℝ, serviceReq ω j ≤ served (schedule σ) j ω t := by
  obtain ⟨T, _, hT⟩ := CMS.drift D.lam D.mu D.lam_pos D.mu_pos D.stable
    (fun k m => ω.1 (k, m)) (fun k m => ω.2.1 (k, m)) (fun k m => (hp1 _).le)
    (fun k m => (hp2 _).le) hx hs (-(arrival ω j))
  obtain ⟨N0, hN0⟩ := hcov T
  have hr : ∀ l, 0 < serviceReq ω l := hp2
  have hA : Abef (FN D.M N0) (arrival ω) (serviceReq ω) T - T < -(arrival ω j) := by
    rw [Abef_FN_eq]; exact hT N0
  obtain ⟨t, ht0, htT, hW⟩ := exists_Wl_zero (FN D.M N0) (arrival ω) (serviceReq ω)
    (fun l _ => (hr l).le) (arrival ω j) T hA
  have hc : Covers (FN D.M) (arrival ω) N0 t := fun l hl => by
    have := hN0 l (le_trans hl htT)
    simp [FN, this]
  refine ⟨t, ?_⟩
  rw [served_eq_servedG σ, served_formula (key_inj σ) (FN_mono D.M) (arrival_nonneg hp1) hr hc j,
    if_pos ht0]
  have h1 : Wl (Le (key σ) (FN D.M) N0 j) (arrival ω) (serviceReq ω) t ≤ 0 := by
    rw [← hW]; exact Wl_mono (Finset.filter_subset _ _) (fun l _ => (hr l).le) t
  have h2 := Wl_nonneg (Lt (key σ) (FN D.M) N0 j) (arrival ω) (serviceReq ω) t
  linarith

theorem ae_good (D : Data) : ∀ᵐ ω ∂D.P, Good ω ∧ (∀ j, 0 < ω.1 j) ∧
    ∀ j : Job D.M, ∀ σ : Equiv.Perm (Fin D.M), ∃ t : ℝ, serviceReq ω j ≤ served (schedule σ) j ω t := by
  filter_upwards [ae_facts D] with ω ⟨hp1, hp2, hcov, hx, hs⟩
  refine ⟨⟨arrival_nonneg hp1, hp2, fun T => ?_⟩, hp1, fun j σ => complete_of D σ hp1 hp2 hcov hx hs j⟩
  obtain ⟨N0, hN0⟩ := hcov T
  exact ⟨N0, fun l hl => by simp [FN, hN0 l hl]⟩

theorem isStrategy_schedule (D : Data) (σ : Equiv.Perm (Fin D.M)) : IsStrategy D (schedule σ) :=
  isStrategy_of_ae D σ (by
    filter_upwards [ae_good D] with ω ⟨hg, hp, hc⟩
    exact ⟨hg, hp, fun j => hc j σ⟩)

theorem isPriority_schedule (D : Data) (σ : Equiv.Perm (Fin D.M)) : IsPriority D σ (schedule σ) :=
  isPriority_of_ae_good D σ (by filter_upwards [ae_good D] with ω h; exact h.1)

end CMB


/-! ## Bridge part 6: the response-time limit (Achieves) via the Mathlib replicas `CMV` -/

namespace CMB
open CoffmanMitrani MeasureTheory ProbabilityTheory

theorem achieves_schedule (D : Data) (σ : Equiv.Perm (Fin D.M)) :
    ∃ W : Fin D.M → ℝ, Achieves D (schedule σ) W := by
  haveI : ∀ k, IsProbabilityMeasure (expMeasure (D.lam k)) :=
    fun k => isProbabilityMeasure_expMeasure (D.lam_pos k)
  haveI : ∀ k, IsProbabilityMeasure (expMeasure (D.mu k)) :=
    fun k => isProbabilityMeasure_expMeasure (D.mu_pos k)
  have hgood : ∀ᵐ ω ∂(CMT.PO (M := D.M) (E := ℕ → unitInterval) (fun k => expMeasure (D.lam k))
      (fun k => expMeasure (D.mu k)) (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))),
      CMV.GoodO ω := by
    show ∀ᵐ ω ∂D.P, CMV.GoodO ω
    filter_upwards [CMP.ae_covers D, ae_pos D] with ω h1 h2
    exact ⟨h1.1, h2.2, h1.2⟩
  have hA := fun i : Fin D.M => CMV.achieves_O σ i D.lam D.mu
    (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)) D.lam_pos D.mu_pos D.stable hgood
  choose W hW using fun i => (hA i).2
  exact ⟨W, fun i => ⟨fun n => (hA i).1 n, hW i⟩⟩

end CMB


set_option autoImplicit false


/-! P1 core of the theorem_2 disproof (pinning): a set `E` of service instants of one job that
satisfies `s ∈ E ↔ s ∈ A ∧ served(s) < x` (served = Lebesgue measure of `E ∩ [0, s)`) is unique
on `[0, ∞)`. Mathlib only; no measurability needed (outer measure). -/

namespace CMP

open MeasureTheory Set

/-- served time of the instant set `E` before `t` -/
noncomputable def F (E : Set ℝ) (t : ℝ) : ℝ := (volume (E ∩ Ico 0 t)).toReal

theorem F_ne_top (E : Set ℝ) (t : ℝ) : volume (E ∩ Ico 0 t) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Ico]) (measure_mono inter_subset_right)

theorem F_mono (E : Set ℝ) {t t' : ℝ} (h : t ≤ t') : F E t ≤ F E t' := by
  unfold F
  exact ENNReal.toReal_mono (F_ne_top E t')
    (measure_mono (inter_subset_inter_right _ (Ico_subset_Ico_right h)))

theorem F_lip (E : Set ℝ) {t t' : ℝ} (h : t ≤ t') : F E t' ≤ F E t + (t' - t) := by
  unfold F
  have hsub : E ∩ Ico 0 t' ⊆ (E ∩ Ico 0 t) ∪ Ico t t' := by
    intro s ⟨hs, h0, h1⟩
    by_cases hst : s < t
    · exact Or.inl ⟨hs, h0, hst⟩
    · exact Or.inr ⟨le_of_not_gt hst, h1⟩
  have h1 : volume (E ∩ Ico 0 t') ≤ volume (E ∩ Ico 0 t) + ENNReal.ofReal (t' - t) := by
    calc volume (E ∩ Ico 0 t') ≤ volume ((E ∩ Ico 0 t) ∪ Ico t t') := measure_mono hsub
      _ ≤ volume (E ∩ Ico 0 t) + volume (Ico t t') := measure_union_le _ _
      _ = volume (E ∩ Ico 0 t) + ENNReal.ofReal (t' - t) := by rw [Real.volume_Ico]
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨F_ne_top E t, ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add (F_ne_top E t) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at h2
  exact h2

theorem F_congr {E1 E2 : Set ℝ} {t : ℝ} (h : ∀ s, 0 ≤ s → s < t → (s ∈ E1 ↔ s ∈ E2)) :
    F E1 t = F E2 t := by
  unfold F
  congr 2
  ext s
  constructor
  · rintro ⟨hs, h0, h1⟩; exact ⟨(h s h0 h1).1 hs, h0, h1⟩
  · rintro ⟨hs, h0, h1⟩; exact ⟨(h s h0 h1).2 hs, h0, h1⟩

/-- Uniqueness of the instant set of a job given its admissible set `A` and requirement `x`. -/
theorem agree_of_fix (A : Set ℝ) (x : ℝ) (E1 E2 : Set ℝ)
    (h1 : ∀ s, s ∈ E1 ↔ s ∈ A ∧ F E1 s < x)
    (h2 : ∀ s, s ∈ E2 ↔ s ∈ A ∧ F E2 s < x) :
    ∀ s, 0 ≤ s → (s ∈ E1 ↔ s ∈ E2) := by
  by_contra hcon
  push_neg at hcon
  set bad : Set ℝ := {s | 0 ≤ s ∧ ¬ (s ∈ E1 ↔ s ∈ E2)} with hbad
  have hne : bad.Nonempty := by
    obtain ⟨s, hs0, hs⟩ := hcon
    exact ⟨s, hs0, fun h => by
      rcases hs with ⟨a, b⟩ | ⟨a, b⟩
      · exact b (h.1 a)
      · exact a (h.2 b)⟩
  have hbdd : BddBelow bad := ⟨0, fun s hs => hs.1⟩
  set τ := sInf bad with hτ
  have hτle : ∀ b ∈ bad, τ ≤ b := fun b hb => csInf_le hbdd hb
  have hτ0 : 0 ≤ τ := le_csInf hne (fun b hb => hb.1)
  -- below τ the sets agree
  have hbelow : ∀ s, 0 ≤ s → s < τ → (s ∈ E1 ↔ s ∈ E2) := by
    intro s hs0 hsτ
    by_contra hns
    exact absurd (hτle s ⟨hs0, hns⟩) (not_le.2 hsτ)
  have hFτ : F E1 τ = F E2 τ := F_congr hbelow
  by_cases hc : F E1 τ < x
  · -- just after τ both sets equal A
    have hε : 0 < x - F E1 τ := by linarith
    obtain ⟨b, hb, hbε⟩ := exists_lt_of_csInf_lt hne (show sInf bad < τ + (x - F E1 τ) by linarith)
    have hτb := hτle b hb
    have hF1 : F E1 b < x := by
      have := F_lip E1 hτb; linarith
    have hF2 : F E2 b < x := by
      have := F_lip E2 hτb; linarith
    apply hb.2
    rw [h1 b, h2 b]
    exact ⟨fun h => ⟨h.1, hF2⟩, fun h => ⟨h.1, hF1⟩⟩
  · -- from τ on, neither set has points
    push_neg at hc
    obtain ⟨b, hb⟩ := hne
    have hτb := hτle b hb
    have hF1 : x ≤ F E1 b := le_trans hc (F_mono E1 hτb)
    have hF2 : x ≤ F E2 b := le_trans (hFτ ▸ hc) (F_mono E2 hτb)
    apply hb.2
    rw [h1 b, h2 b]
    exact ⟨fun h => absurd h.2 (not_lt.2 hF1), fun h => absurd h.2 (not_lt.2 hF2)⟩

theorem F_eq_of_fix (A : Set ℝ) (x : ℝ) (E1 E2 : Set ℝ)
    (h1 : ∀ s, s ∈ E1 ↔ s ∈ A ∧ F E1 s < x)
    (h2 : ∀ s, s ∈ E2 ↔ s ∈ A ∧ F E2 s < x) (t : ℝ) : F E1 t = F E2 t :=
  F_congr (fun s hs0 _ => agree_of_fix A x E1 E2 h1 h2 s hs0)

end CMP

namespace CMP

open CoffmanMitrani MeasureTheory Set

/-- With one class, the priority clause, feasibility and non-idling pin down when job `j` is
served: exactly when it is present and no lower-index job is present. -/
theorem some_iff {S : Schedule 1} {ω : Omega 1}
    (c2 : ∀ (t : ℝ) (j : Job 1), S ω t = some j → present S j ω t)
    (c3 : ∀ t : ℝ, S ω t = none ↔ ∀ j : Job 1, ¬ present S j ω t)
    (pr : ∀ (t : ℝ) (j j' : Job 1), S ω t = some j → present S j' ω t → j.2 ≤ j'.2)
    (t : ℝ) (j : Job 1) :
    S ω t = some j ↔ present S j ω t ∧ ∀ k : Job 1, k.2 < j.2 → ¬ present S k ω t := by
  constructor
  · intro h
    exact ⟨c2 t j h, fun k hk hpk => absurd (pr t j k h hpk) (not_le.2 hk)⟩
  · rintro ⟨hj, hlow⟩
    cases hS : S ω t with
    | none => exact absurd hj ((c3 t).1 hS j)
    | some i =>
      have hi := c2 t i hS
      have hij := pr t i j hS hj
      rcases lt_or_eq_of_le hij with hlt | heq
      · exact absurd hi (hlow i hlt)
      · have : i = j := Prod.ext (Subsingleton.elim _ _) heq
        rw [this]

theorem job_eq (k : Job 1) : k = (0, k.2) := Prod.ext (Subsingleton.elim _ _) rfl

/-- Pinning: two one-class schedules satisfying clauses 2, 3 and the priority clause at `ω`
serve every job the same amount by every time. -/
theorem served_pin {S T : Schedule 1} {ω : Omega 1}
    (c2S : ∀ (t : ℝ) (j : Job 1), S ω t = some j → present S j ω t)
    (c3S : ∀ t : ℝ, S ω t = none ↔ ∀ j : Job 1, ¬ present S j ω t)
    (prS : ∀ (t : ℝ) (j j' : Job 1), S ω t = some j → present S j' ω t → j.2 ≤ j'.2)
    (c2T : ∀ (t : ℝ) (j : Job 1), T ω t = some j → present T j ω t)
    (c3T : ∀ t : ℝ, T ω t = none ↔ ∀ j : Job 1, ¬ present T j ω t)
    (prT : ∀ (t : ℝ) (j j' : Job 1), T ω t = some j → present T j' ω t → j.2 ≤ j'.2) :
    ∀ (j : Job 1) (t : ℝ), served S j ω t = served T j ω t := by
  have key : ∀ n : ℕ, ∀ t, served S (0, n) ω t = served T (0, n) ω t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hlow : ∀ (k : Job 1) (s : ℝ), k.2 < n → (present S k ω s ↔ present T k ω s) := by
        intro k s hk
        rw [job_eq k]
        unfold present
        rw [ih k.2 hk s]
      let A : Set ℝ := {s | arrival ω (0, n) ≤ s ∧ ∀ k : Job 1, k.2 < n → ¬ present S k ω s}
      have hS : ∀ s, s ∈ {s | S ω s = some (0, n)} ↔ s ∈ A ∧ F {s | S ω s = some (0, n)} s <
          serviceReq ω (0, n) := by
        intro s
        show S ω s = some (0, n) ↔ _
        rw [some_iff c2S c3S prS s (0, n)]
        unfold present
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
      have hT : ∀ s, s ∈ {s | T ω s = some (0, n)} ↔ s ∈ A ∧ F {s | T ω s = some (0, n)} s <
          serviceReq ω (0, n) := by
        intro s
        show T ω s = some (0, n) ↔ _
        rw [some_iff c2T c3T prT s (0, n)]
        have hA : (∀ k : Job 1, k.2 < (0, n).2 → ¬ present T k ω s) ↔
            (∀ k : Job 1, k.2 < n → ¬ present S k ω s) :=
          ⟨fun h k hk => by rw [hlow k s hk]; exact h k hk,
           fun h k hk => by rw [← hlow k s hk]; exact h k hk⟩
        rw [hA]
        unfold present
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
      intro t
      exact F_eq_of_fix A (serviceReq ω (0, n)) _ _ hS hT t
  intro j t
  rw [job_eq j]
  exact key j.2 t

theorem responseTime_pin {S T : Schedule 1} {ω : Omega 1}
    (h : ∀ (j : Job 1) (t : ℝ), served S j ω t = served T j ω t) (j : Job 1) :
    responseTime S j ω = responseTime T j ω := by
  unfold responseTime departure
  simp only [h]

end CMP


/-! Disproof skeleton for `CoffmanMitrani.theorem_2` (1dad8aff). The forward direction fails as
formalized (IsStrategy clause 5 is vacuous, see scratch/decomp/CM_FAMILY_FALSE_1104.md).
Glue: if every priority strategy achieves the same vector `P0` (pinning, true for `M = 1`) and
some strategy achieves `W' ≠ P0`, the characterization fails for `D`. -/

namespace CMDP

open CoffmanMitrani

/-- Every element of `H D` equals `P0` once every priority strategy achieves only `P0`. -/
theorem mem_H_eq (D : Data) (P0 : Fin D.M → ℝ)
    (hpin : ∀ (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M) (Pv : Fin D.M → ℝ),
      IsPriority D σ S → IsStrategy D S → Achieves D S Pv → Pv = P0)
    (W : Fin D.M → ℝ) (hW : W ∈ H D) : W = P0 := by
  obtain ⟨π, Pv, α, hS, _hα, hsum, hWeq⟩ := hW
  have hP : ∀ m, Pv m = P0 := by
    intro m
    obtain ⟨S, h1, h2, h3⟩ := hS m
    exact hpin (π m) S (Pv m) h1 h2 h3
  rw [hWeq]
  simp only [hP]
  rw [← Finset.sum_smul, hsum, one_smul]

/-- The glue: pinning plus one achievable vector off `P0` refutes the characterization at `D`. -/
theorem not_char (D : Data) (P0 W' : Fin D.M → ℝ)
    (hpin : ∀ (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M) (Pv : Fin D.M → ℝ),
      IsPriority D σ S → IsStrategy D S → Achieves D S Pv → Pv = P0)
    (hach : Achievable D W') (hne : W' ≠ P0) :
    ¬ (∀ W : Fin D.M → ℝ, Achievable D W ↔ W ∈ H D) := by
  intro h
  exact hne (mem_H_eq D P0 hpin W' ((h W').1 hach))

/-- The `M = 1` model used for the counterexample: `λ = 1`, `μ = 2`. -/
@[reducible] def D1 : Data where
  M := 1
  lam := fun _ => 1
  mu := fun _ => 2
  one_le_M := le_rfl
  lam_pos := fun _ => one_pos
  mu_pos := fun _ => two_pos
  stable := by norm_num

end CMDP


namespace CMDP

open CoffmanMitrani MeasureTheory

/-- With one class, two priority strategies achieve the same vector. -/
theorem pin_vec (σ τ : Equiv.Perm (Fin D1.M)) (S T : Schedule D1.M) (Pv Pv' : Fin D1.M → ℝ)
    (hSp : IsPriority D1 σ S) (hSs : IsStrategy D1 S) (hA : Achieves D1 S Pv)
    (hTp : IsPriority D1 τ T) (hTs : IsStrategy D1 T) (hB : Achieves D1 T Pv') : Pv = Pv' := by
  have fin1 : ∀ a b : Fin D1.M, a = b := fun a b =>
    Fin.ext (by have ha := a.2; have hb := b.2; simp only [D1] at ha hb; omega)
  obtain ⟨ruleS, hS⟩ := hSs.2
  obtain ⟨ruleT, hT⟩ := hTs.2
  have hae : ∀ᵐ ω ∂D1.P, ∀ j : Job D1.M, responseTime S j ω = responseTime T j ω := by
    filter_upwards [hS, hT, hSp, hTp] with ω hs ht hps hpt
    have prS : ∀ (t : ℝ) (j j' : Job 1), S ω t = some j → present S j' ω t → j.2 ≤ j'.2 := by
      intro t j j' h1 h2
      rcases hps t j j' h1 h2 with h | h
      · exact absurd h (by rw [fin1 (σ.symm j.1) (σ.symm j'.1)]; exact lt_irrefl _)
      · exact h.2
    have prT : ∀ (t : ℝ) (j j' : Job 1), T ω t = some j → present T j' ω t → j.2 ≤ j'.2 := by
      intro t j j' h1 h2
      rcases hpt t j j' h1 h2 with h | h
      · exact absurd h (by rw [fin1 (τ.symm j.1) (τ.symm j'.1)]; exact lt_irrefl _)
      · exact h.2
    exact CMP.responseTime_pin (CMP.served_pin hs.1 hs.2.1 prS ht.1 ht.2.1 prT)
  funext i
  have hint : ∀ n : ℕ, ∫ ω, responseTime S (i, n) ω ∂D1.P = ∫ ω, responseTime T (i, n) ω ∂D1.P :=
    fun n => integral_congr_ae (hae.mono fun ω h => h (i, n))
  have h1 := (hA i).2
  have h2 := (hB i).2
  simp only [hint] at h1
  exact tendsto_nhds_unique h1 h2

end CMDP

open CoffmanMitrani in
/-- Conditional form of the disproof (both children as hypotheses). -/
theorem dp_conditional (P0 W' : Fin CMDP.D1.M → ℝ)
    (hpin : ∀ (σ : Equiv.Perm (Fin CMDP.D1.M)) (S : Schedule CMDP.D1.M) (Pv : Fin CMDP.D1.M → ℝ),
      IsPriority CMDP.D1 σ S → IsStrategy CMDP.D1 S → Achieves CMDP.D1 S Pv → Pv = P0)
    (hach : Achievable CMDP.D1 W') (hne : W' ≠ P0) :
    ¬ (∀ (D : Data) (W : Fin D.M → ℝ), Achievable D W ↔ W ∈ H D) := by
  intro h
  exact CMDP.not_char CMDP.D1 P0 W' hpin hach hne (h CMDP.D1)

set_option autoImplicit false

/-! P2 of the theorem_2 disproof (1dad8aff): an anticipating schedule on one class that passes
`IsStrategy` through the inertia rule. Part CMI: the inertia rule and the generic clause-5 lemma. -/

namespace CMI

open CoffmanMitrani Set

open Classical in
/-- Inertia rule: keep serving the job served just before if it is still present, else serve the
lowest-rank present job, else idle. -/
noncomputable def irule (h : History 1) (_ : ℕ → unitInterval) : Option (Fin 1 × ℕ) :=
  if hq : ∃ p : Fin 1 × ℕ, (∃ δ > 0, ∀ s ∈ Ioo (h.elapsed - δ) h.elapsed, h.schedule s = some p) ∧
      h.arrivals p ≠ none ∧ h.departures p = none then some hq.choose
  else if hr : ∃ r : ℕ, h.arrivals (0, r) ≠ none ∧ h.departures (0, r) = none then
    some (0, Nat.find hr)
  else none

theorem fin1 (i : Fin 1) : i = 0 := Subsingleton.elim _ _

theorem hist_pres {S : Schedule 1} {ω : Omega 1} {j0 : Job 1} {t : ℝ}
    (hoff : classOffset ω j0 0 = j0.2) (p : Fin 1 × ℕ) :
    ((history S ω j0 t).arrivals p ≠ none ∧ (history S ω j0 t).departures p = none) ↔
      present S (0, j0.2 + p.2) ω t := by
  have hp : p.1 = 0 := fin1 _
  simp only [history, present, hp, hoff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact h1 (if_neg hc)
    · by_contra hc
      rw [if_pos (le_of_not_gt hc)] at h2
      simp at h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [if_pos h1]
      simp
    · rw [if_neg (not_le.2 h2)]

theorem hist_sched {S : Schedule 1} {ω : Omega 1} {j0 : Job 1} {t s : ℝ} (h0 : 0 ≤ s)
    (h1 : s < t - arrival ω j0) :
    (history S ω j0 t).schedule s =
      (S ω (arrival ω j0 + s)).map (fun j => (j.1, j.2 - classOffset ω j0 j.1)) := by
  simp only [history]
  rw [if_pos ⟨h0, h1⟩]

theorem hist_sched_neg {S : Schedule 1} {ω : Omega 1} {j0 : Job 1} {t s : ℝ} (h0 : s < 0) :
    (history S ω j0 t).schedule s = none := by
  simp only [history]
  rw [if_neg (fun h => absurd h.1 (not_le.2 h0))]

/-- Generic clause 5 for the inertia rule (one class). -/
theorem clause5 {S : Schedule 1} {ω : Omega 1} (j0 : Job 1)
    (hoff : classOffset ω j0 0 = j0.2)
    (hmono : ∀ k : Job 1, j0.2 ≤ k.2 → arrival ω j0 ≤ arrival ω k)
    (hc2 : ∀ (t : ℝ) (j : Job 1), S ω t = some j → present S j ω t)
    (hold : ∀ (k : Job 1) (t : ℝ), k.2 < j0.2 → arrival ω j0 ≤ t → ¬ present S k ω t)
    (hL : ∀ (t : ℝ) (q : Job 1) (δ : ℝ), 0 < δ → (∀ u ∈ Ioo (t - δ) t, S ω u = some q) →
      present S q ω t → S ω t = some q)
    (hLow : ∀ t : ℝ,
      (¬ ∃ q : Job 1, ∃ δ > 0, (∀ u ∈ Ioo (t - δ) t, S ω u = some q) ∧ present S q ω t) →
      ∀ j : Job 1, present S j ω t → (∀ k : Job 1, k.2 < j.2 → ¬ present S k ω t) →
        S ω t = some j)
    (hnone : ∀ t : ℝ, (∀ j : Job 1, ¬ present S j ω t) → S ω t = none)
    (t : ℝ) (ht : arrival ω j0 ≤ t) :
    S ω t = (irule (history S ω j0 t) (seed ω j0)).map
      (fun p => (p.1, classOffset ω j0 p.1 + p.2)) := by
  have hoff' : ∀ i : Fin 1, classOffset ω j0 i = j0.2 := fun i => by rw [fin1 i]; exact hoff
  have hge : ∀ (u : ℝ) (k : Job 1), arrival ω j0 ≤ u → S ω u = some k → j0.2 ≤ k.2 := by
    intro u k hu hk
    by_contra hlt
    exact hold k u (not_le.1 hlt) hu (hc2 u k hk)
  have hel : (history S ω j0 t).elapsed = t - arrival ω j0 := rfl
  unfold irule
  by_cases hq : ∃ p : Fin 1 × ℕ, (∃ δ > 0, ∀ s ∈ Ioo ((history S ω j0 t).elapsed - δ)
      (history S ω j0 t).elapsed, (history S ω j0 t).schedule s = some p) ∧
      (history S ω j0 t).arrivals p ≠ none ∧ (history S ω j0 t).departures p = none
  · rw [dif_pos hq]
    obtain ⟨⟨δ, hδ, hs0⟩, hpres⟩ := hq.choose_spec
    have hs : ∀ s ∈ Ioo ((t - arrival ω j0) - δ) (t - arrival ω j0),
        (history S ω j0 t).schedule s = some hq.choose := hs0
    have hpos : 0 < t - arrival ω j0 := by
      by_contra hle
      push_neg at hle
      have hmem : (t - arrival ω j0) - δ / 2 ∈
          Ioo ((t - arrival ω j0) - δ) (t - arrival ω j0) := ⟨by linarith, by linarith⟩
      have h1 := hs _ hmem
      rw [hist_sched_neg (by linarith)] at h1
      simp at h1
    have m1 := min_le_left δ (t - arrival ω j0)
    have m2 := min_le_right δ (t - arrival ω j0)
    have hq' : ∀ u ∈ Ioo (t - min δ (t - arrival ω j0)) t,
        S ω u = some (0, j0.2 + hq.choose.2) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := hu
      have hb : arrival ω j0 ≤ u := by linarith
      have hmem : u - arrival ω j0 ∈ Ioo ((t - arrival ω j0) - δ) (t - arrival ω j0) :=
        ⟨by linarith, by linarith⟩
      have h1 := hs _ hmem
      rw [hist_sched (by linarith) (by linarith),
        show arrival ω j0 + (u - arrival ω j0) = u by ring] at h1
      cases hSu : S ω u with
      | none => rw [hSu] at h1; simp at h1
      | some k =>
        rw [hSu] at h1
        have hk := hge u k hb hSu
        simp only [Option.map_some, Option.some.injEq] at h1
        rw [hoff' k.1] at h1
        rw [← h1]
        exact congrArg some (Prod.ext (fin1 k.1) (by show k.2 = j0.2 + (k.2 - j0.2); omega))
    have hpq := (hist_pres hoff hq.choose).1 hpres
    rw [hL t _ _ (lt_min hδ hpos) hq' hpq, Option.map_some, hoff' hq.choose.1]
    exact congrArg some (Prod.ext (fin1 _).symm rfl)
  · rw [dif_neg hq]
    have hnoS : ¬ ∃ q : Job 1, ∃ δ > 0, (∀ u ∈ Ioo (t - δ) t, S ω u = some q) ∧
        present S q ω t := by
      rintro ⟨q, δ, hδ, hu, hqp⟩
      have hq2 : j0.2 ≤ q.2 := by
        by_contra h
        exact hold q t (not_le.1 h) ht hqp
      have hpos : 0 < t - arrival ω j0 := by
        by_contra hle
        push_neg at hle
        have hmem : t - δ / 2 ∈ Ioo (t - δ) t := ⟨by linarith, by linarith⟩
        have h1 := (hc2 _ _ (hu _ hmem)).1
        have h2 := hmono q hq2
        linarith
      apply hq
      have m1 := min_le_left δ (t - arrival ω j0)
      have m2 := min_le_right δ (t - arrival ω j0)
      refine ⟨(0, q.2 - j0.2), ⟨min δ (t - arrival ω j0), lt_min hδ hpos, ?_⟩, ?_⟩
      · intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        rw [hel] at hs1 hs2
        rw [hist_sched (by linarith) hs2, hu _ ⟨by linarith, by linarith⟩, Option.map_some,
          hoff' q.1, fin1 q.1]
      · rw [hist_pres hoff]
        have : ((0 : Fin 1), j0.2 + ((0 : Fin 1), q.2 - j0.2).2) = q :=
          Prod.ext (fin1 q.1).symm (by show j0.2 + (q.2 - j0.2) = q.2; omega)
        rw [this]
        exact hqp
    have hlow := hLow t hnoS
    by_cases hr : ∃ r : ℕ, (history S ω j0 t).arrivals (0, r) ≠ none ∧
        (history S ω j0 t).departures (0, r) = none
    · rw [dif_pos hr, Option.map_some, hoff' 0]
      apply hlow
      · exact (hist_pres hoff (0, Nat.find hr)).1 (Nat.find_spec hr)
      · intro k hk hkp
        have hk' : k.2 < j0.2 + Nat.find hr := hk
        by_cases hk0 : k.2 < j0.2
        · exact hold k t hk0 ht hkp
        · have hlt : k.2 - j0.2 < Nat.find hr := by omega
          apply Nat.find_min hr hlt
          rw [hist_pres hoff]
          have : ((0 : Fin 1), j0.2 + ((0 : Fin 1), k.2 - j0.2).2) = k :=
            Prod.ext (fin1 k.1).symm (by show j0.2 + (k.2 - j0.2) = k.2; omega)
          rw [this]
          exact hkp
    · rw [dif_neg hr]
      apply hnone
      intro k hkp
      by_cases hk0 : k.2 < j0.2
      · exact hold k t hk0 ht hkp
      · apply hr
        refine ⟨k.2 - j0.2, ?_⟩
        rw [hist_pres hoff]
        have : ((0 : Fin 1), j0.2 + ((0 : Fin 1), k.2 - j0.2).2) = k :=
          Prod.ext (fin1 k.1).symm (by show j0.2 + (k.2 - j0.2) = k.2; omega)
        rw [this]
        exact hkp

end CMI

/-! Part CMX: the swap schedule on one class. FCFS start times `fs`, and for a swap predicate `sw`
(job `m + 1` is served before job `m`, in the window `(fs m, fs m + x (m+1))`), the job `k` is
served on `[u k, v k)` with `v k - u k = x k`. -/

namespace CMX
set_option linter.unusedSectionVars false

open CoffmanMitrani Set

section
variable (ω : Omega 1)

noncomputable def x (k : ℕ) : ℝ := ω.2.1 (0, k)
noncomputable def τ (k : ℕ) : ℝ := ω.1 (0, k)
noncomputable def a (k : ℕ) : ℝ := arrival ω (0, k)

noncomputable def fs : ℕ → ℝ
  | 0 => a ω 0
  | k + 1 => max (a ω (k + 1)) (fs k + x ω k)

noncomputable def d (k : ℕ) : ℝ := fs ω k + x ω k

variable (sw : ℕ → Prop)

open Classical in
noncomputable def v (k : ℕ) : ℝ :=
  if sw k then d ω (k + 1) else if (∃ m, k = m + 1 ∧ sw m) then fs ω (k - 1) + x ω k else d ω k

noncomputable def u (k : ℕ) : ℝ := v ω sw k - x ω k

def P (k : ℕ) (t : ℝ) : Prop := a ω k ≤ t ∧ t < v ω sw k

def Win (m : ℕ) (t : ℝ) : Prop := sw m ∧ fs ω m < t ∧ t < fs ω m + x ω (m + 1)

/-- hypotheses on a sample point and a swap predicate -/
structure Hyp : Prop where
  tpos : ∀ k, 0 < τ ω k
  xpos : ∀ k, 0 < x ω k
  arr : ∀ m, sw m → a ω (m + 1) ≤ fs ω m
  lt : ∀ m, sw m → x ω (m + 1) < x ω m
  nn : ∀ m, sw m → ¬ sw (m + 1)

end

open Classical in
noncomputable def sch (SW : Omega 1 → ℕ → Prop) : Schedule 1 := fun ω t =>
  if h : ∃ m, Win ω (SW ω) m t then some (0, Nat.find h + 1)
  else if h2 : ∃ k, P ω (SW ω) k t then some (0, Nat.find h2) else none

section
variable {ω : Omega 1}

theorem a_succ (k : ℕ) : a ω (k + 1) = a ω k + τ ω (k + 1) := by
  simp only [a, arrival, τ]
  rw [Finset.sum_range_succ]

theorem a_zero : a ω 0 = τ ω 0 := by
  simp [a, arrival, τ]

theorem fs_succ (k : ℕ) : fs ω (k + 1) = max (a ω (k + 1)) (d ω k) := rfl

theorem a_le_fs (k : ℕ) : a ω k ≤ fs ω k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

theorem d_le_fs_succ (k : ℕ) : d ω k ≤ fs ω (k + 1) := le_max_right _ _

variable {sw : ℕ → Prop} (h : Hyp ω sw)
include h

theorem a_strictMono : StrictMono (a ω) :=
  strictMono_nat_of_lt_succ fun k => by rw [a_succ]; linarith [h.tpos (k + 1)]

theorem a_pos (k : ℕ) : 0 < a ω k := by
  induction k with
  | zero => rw [a_zero]; exact h.tpos 0
  | succ k ih => rw [a_succ]; linarith [h.tpos (k + 1)]

theorem fs_lt_d (k : ℕ) : fs ω k < d ω k := by unfold d; linarith [h.xpos k]

theorem fs_mono : Monotone (fs ω) :=
  monotone_nat_of_le_succ fun k => (fs_lt_d h k).le.trans (d_le_fs_succ k)

theorem d_le_fs {i j : ℕ} (hij : i < j) : d ω i ≤ fs ω j :=
  (d_le_fs_succ i).trans (fs_mono h (Nat.succ_le_of_lt hij))

theorem fs_pos (k : ℕ) : 0 < fs ω k := (a_pos h k).trans_le (a_le_fs k)

theorem fs_succ_sw {m : ℕ} (hm : sw m) : fs ω (m + 1) = d ω m :=
  max_eq_right ((h.arr m hm).trans (fs_lt_d h m).le)

theorem v_A {k : ℕ} (hk : sw k) : v ω sw k = d ω (k + 1) := by
  unfold v; rw [if_pos hk]

theorem v_B {m : ℕ} (hm : sw m) : v ω sw (m + 1) = fs ω m + x ω (m + 1) := by
  unfold v
  rw [if_neg (h.nn m hm), if_pos ⟨m, rfl, hm⟩]
  simp

theorem v_C {k : ℕ} (h1 : ¬ sw k) (h2 : ¬ ∃ m, k = m + 1 ∧ sw m) : v ω sw k = d ω k := by
  unfold v; rw [if_neg h1, if_neg h2]

theorem u_A {k : ℕ} (hk : sw k) : u ω sw k = fs ω k + x ω (k + 1) := by
  unfold u; rw [v_A h hk]; unfold d; rw [fs_succ_sw h hk]; unfold d; ring

theorem u_B {m : ℕ} (hm : sw m) : u ω sw (m + 1) = fs ω m := by
  unfold u; rw [v_B h hm]; ring

theorem u_C {k : ℕ} (h1 : ¬ sw k) (h2 : ¬ ∃ m, k = m + 1 ∧ sw m) : u ω sw k = fs ω k := by
  unfold u; rw [v_C h h1 h2]; unfold d; ring

theorem v_le_d {k : ℕ} (hk : ¬ sw k) : v ω sw k ≤ d ω k := by
  by_cases h2 : ∃ m, k = m + 1 ∧ sw m
  · obtain ⟨m, rfl, hm⟩ := h2
    rw [v_B h hm]
    have := d_le_fs_succ (ω := ω) m
    unfold d at this ⊢
    linarith [h.xpos m]
  · rw [v_C h hk h2]

theorem before_slot {i j : ℕ} (hij : i < j) (hex : ¬ (i + 1 = j ∧ sw i)) : v ω sw i ≤ fs ω j := by
  by_cases hi : sw i
  · rw [v_A h hi]
    have : i + 1 < j := by
      rcases Nat.lt_or_ge (i + 1) j with h' | h'
      · exact h'
      · exact absurd ⟨by omega, hi⟩ hex
    exact d_le_fs h this
  · exact (v_le_d h hi).trans (d_le_fs_succ i |>.trans (fs_mono h (Nat.succ_le_of_lt hij)))

theorem slot_unique {m j : ℕ} {t : ℝ} (h1 : fs ω m ≤ t) (h2 : t < d ω m) (h3 : fs ω j ≤ t)
    (h4 : t < d ω j) : m = j := by
  rcases lt_trichotomy m j with hmj | hmj | hmj
  · have := d_le_fs h hmj; linarith
  · exact hmj
  · have := d_le_fs h hmj; linarith

theorem win_slot {m : ℕ} {t : ℝ} (hw : Win ω sw m t) : fs ω m < t ∧ t < d ω m := by
  obtain ⟨hm, h1, h2⟩ := hw
  refine ⟨h1, ?_⟩
  unfold d
  linarith [h.lt m hm]

theorem win_unique {m m' : ℕ} {t : ℝ} (hw : Win ω sw m t) (hw' : Win ω sw m' t) : m = m' := by
  have a1 := win_slot h hw
  have a2 := win_slot h hw'
  exact slot_unique h a1.1.le a1.2 a2.1.le a2.2

theorem win_P {m : ℕ} {t : ℝ} (hw : Win ω sw m t) : P ω sw (m + 1) t := by
  obtain ⟨hm, h1, h2⟩ := hw
  refine ⟨(h.arr m hm).trans h1.le, ?_⟩
  rw [v_B h hm]
  exact h2

end

section
open Classical
variable {SW : Omega 1 → ℕ → Prop} {ω : Omega 1}

theorem sch_win {m : ℕ} {t : ℝ} (h : Hyp ω (SW ω)) (hw : Win ω (SW ω) m t) :
    sch SW ω t = some (0, m + 1) := by
  unfold sch
  rw [dif_pos ⟨m, hw⟩]
  have : Nat.find (⟨m, hw⟩ : ∃ m, Win ω (SW ω) m t) = m :=
    (Nat.find_eq_iff _).2 ⟨hw, fun i hi hwi => by have := win_unique h hwi hw; omega⟩
  rw [this]

theorem sch_low {j : ℕ} {t : ℝ} (hW : ¬ ∃ m, Win ω (SW ω) m t) (hP : P ω (SW ω) j t)
    (hlow : ∀ i < j, ¬ P ω (SW ω) i t) : sch SW ω t = some (0, j) := by
  unfold sch
  rw [dif_neg hW, dif_pos ⟨j, hP⟩]
  have : Nat.find (⟨j, hP⟩ : ∃ k, P ω (SW ω) k t) = j :=
    (Nat.find_eq_iff _).2 ⟨hP, fun i hi => hlow i hi⟩
  rw [this]

/-- K1: inside `(u j, v j)` the schedule serves `j`. -/
theorem sch_of_mem (h : Hyp ω (SW ω)) {j : ℕ} {t : ℝ} (h1 : u ω (SW ω) j < t)
    (h2 : t < v ω (SW ω) j) : sch SW ω t = some (0, j) := by
  by_cases hA : SW ω j
  · rw [u_A h hA] at h1
    rw [v_A h hA] at h2
    have hfs : fs ω j < t := by linarith [h.xpos (j + 1)]
    have hW : ¬ ∃ m, Win ω (SW ω) m t := by
      rintro ⟨m, hw⟩
      have hs := win_slot h hw
      rcases lt_or_ge t (d ω j) with htd | htd
      · have := slot_unique h hs.1.le hs.2 hfs.le htd
        subst this
        exact absurd hw.2.2 (not_lt.2 h1.le)
      · have hj1 : fs ω (j + 1) ≤ t := by rw [fs_succ_sw h hA]; exact htd
        have := slot_unique h hs.1.le hs.2 hj1 h2
        subst this
        exact h.nn j hA hw.1
    apply sch_low hW ⟨(a_le_fs j).trans hfs.le, by rw [v_A h hA]; exact h2⟩
    intro i hi hPi
    have := before_slot h hi (fun hh => h.nn i hh.2 (by rw [hh.1]; exact hA))
    linarith [hPi.2]
  · by_cases hB : ∃ m, j = m + 1 ∧ SW ω m
    · obtain ⟨m, rfl, hm⟩ := hB
      rw [u_B h hm] at h1
      rw [v_B h hm] at h2
      exact sch_win h ⟨hm, h1, h2⟩
    · rw [u_C h hA hB] at h1
      have h2' := h2
      rw [v_C h hA hB] at h2'
      have hW : ¬ ∃ m, Win ω (SW ω) m t := by
        rintro ⟨m, hw⟩
        have hs := win_slot h hw
        have := slot_unique h hs.1.le hs.2 h1.le h2'
        subst this
        exact hA hw.1
      apply sch_low hW ⟨(a_le_fs j).trans h1.le, h2⟩
      intro i hi hPi
      have := before_slot h hi (fun hh => hB ⟨i, hh.1.symm, hh.2⟩)
      linarith [hPi.2]

theorem ge_fs (h : Hyp ω (SW ω)) {j : ℕ} {t : ℝ} (hP : P ω (SW ω) j t)
    (hlow : ∀ i < j, ¬ P ω (SW ω) i t) (hB : ¬ ∃ m, j = m + 1 ∧ SW ω m) : fs ω j ≤ t := by
  cases j with
  | zero => exact hP.1
  | succ k =>
    rw [fs_succ]
    refine max_le hP.1 ?_
    have hk : ¬ SW ω k := fun hk => hB ⟨k, rfl, hk⟩
    have hak : a ω k ≤ t := ((a_strictMono h).monotone (Nat.le_succ k)).trans hP.1
    have hvk : v ω (SW ω) k ≤ t := by
      by_contra hc
      exact hlow k (Nat.lt_succ_self k) ⟨hak, not_le.1 hc⟩
    by_cases hB' : ∃ m, k = m + 1 ∧ SW ω m
    · obtain ⟨m, rfl, hm⟩ := hB'
      have ham : a ω m ≤ t := ((a_strictMono h).monotone (by omega)).trans hP.1
      have hvm : v ω (SW ω) m ≤ t := by
        by_contra hc
        exact hlow m (by omega) ⟨ham, not_le.1 hc⟩
      rw [v_A h hm] at hvm
      exact hvm
    · rw [v_C h hk hB'] at hvk
      exact hvk

/-- K2: where the schedule serves `j`, `j` is pending and `t ≥ u j` or `t = fs j`. -/
theorem mem_of_sch (h : Hyp ω (SW ω)) {j : ℕ} {t : ℝ} (hs : sch SW ω t = some (0, j)) :
    P ω (SW ω) j t ∧ (u ω (SW ω) j ≤ t ∨ t = fs ω j) := by
  unfold sch at hs
  by_cases hW : ∃ m, Win ω (SW ω) m t
  · rw [dif_pos hW] at hs
    have hj : Nat.find hW + 1 = j := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      exact hs.2
    have hw := Nat.find_spec hW
    rw [← hj]
    refine ⟨win_P h hw, Or.inl ?_⟩
    rw [u_B h hw.1]
    exact hw.2.1.le
  · rw [dif_neg hW] at hs
    by_cases hP : ∃ k, P ω (SW ω) k t
    · rw [dif_pos hP] at hs
      have hj : Nat.find hP = j := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        exact hs.2
      have hPj : P ω (SW ω) j t := hj ▸ Nat.find_spec hP
      have hlow : ∀ i < j, ¬ P ω (SW ω) i t := fun i hi => by
        rw [← hj] at hi
        exact Nat.find_min hP hi
      refine ⟨hPj, ?_⟩
      by_cases hB : ∃ m, j = m + 1 ∧ SW ω m
      · exfalso
        obtain ⟨m, rfl, hm⟩ := hB
        have ham : a ω m ≤ t := ((a_strictMono h).monotone (Nat.le_succ m)).trans hPj.1
        have hvm : v ω (SW ω) m ≤ t := by
          by_contra hc
          exact hlow m (Nat.lt_succ_self m) ⟨ham, not_le.1 hc⟩
        have h2 := hPj.2
        rw [v_A h hm] at hvm
        rw [v_B h hm] at h2
        unfold d at hvm
        rw [fs_succ_sw h hm] at hvm
        unfold d at hvm
        linarith [h.xpos m]
      · have hge := ge_fs h hPj hlow hB
        by_cases hA : SW ω j
        · rw [u_A h hA]
          by_cases hlt : fs ω j < t
          · left
            by_contra hc
            exact hW ⟨j, hA, hlt, not_le.1 hc⟩
          · right
            exact le_antisymm (not_lt.1 hlt) hge
        · left
          rw [u_C h hA hB]
          exact hge
    · rw [dif_neg hP] at hs
      simp at hs

end

end CMX

/-! Part CMX (continued): served time, present, departure, and the clauses 2-5 pathwise. -/

namespace CMX
set_option linter.unusedSectionVars false

open CoffmanMitrani Set MeasureTheory

theorem job1 (k : Job 1) : k = (0, k.2) := Prod.ext (CMI.fin1 _) rfl

section
open Classical
variable {SW : Omega 1 → ℕ → Prop} {ω : Omega 1}

theorem u_pos (h : Hyp ω (SW ω)) (j : ℕ) : 0 < u ω (SW ω) j := by
  by_cases hA : SW ω j
  · rw [u_A h hA]; linarith [fs_pos h j, h.xpos (j + 1)]
  · by_cases hB : ∃ m, j = m + 1 ∧ SW ω m
    · obtain ⟨m, rfl, hm⟩ := hB
      rw [u_B h hm]; exact fs_pos h m
    · rw [u_C h hA hB]; exact fs_pos h j

theorem x_eq (j : ℕ) : x ω j = v ω (SW ω) j - u ω (SW ω) j := by unfold u; ring

theorem served_eq (h : Hyp ω (SW ω)) (j : ℕ) (t : ℝ) :
    served (sch SW) (0, j) ω t = max (min (v ω (SW ω) j) t - u ω (SW ω) j) 0 := by
  unfold served
  set A := {s : ℝ | sch SW ω s = some (0, j)}
  have hsub1 : Ioo (u ω (SW ω) j) (v ω (SW ω) j) ⊆ A := fun s hs => sch_of_mem h hs.1 hs.2
  have hsub2 : A ⊆ Ioo (u ω (SW ω) j) (v ω (SW ω) j) ∪ {u ω (SW ω) j, fs ω j} := by
    intro s hs
    obtain ⟨hP, h2⟩ := mem_of_sch h hs
    rcases h2 with h2 | h2
    · rcases lt_or_eq_of_le h2 with h3 | h3
      · exact Or.inl ⟨h3, hP.2⟩
      · exact Or.inr (Or.inl h3.symm)
    · exact Or.inr (Or.inr h2)
  have hfin : volume ({u ω (SW ω) j, fs ω j} : Set ℝ) = 0 :=
    (Set.toFinite _).measure_zero volume
  have hvol : volume (A ∩ Ico 0 t) = volume (Ioo (u ω (SW ω) j) (v ω (SW ω) j) ∩ Ico 0 t) := by
    apply le_antisymm
    · calc volume (A ∩ Ico 0 t)
          ≤ volume ((Ioo (u ω (SW ω) j) (v ω (SW ω) j) ∩ Ico 0 t) ∪ {u ω (SW ω) j, fs ω j}) := by
            apply measure_mono
            intro s ⟨hs1, hs2⟩
            rcases hsub2 hs1 with h3 | h3
            · exact Or.inl ⟨h3, hs2⟩
            · exact Or.inr h3
        _ ≤ volume (Ioo (u ω (SW ω) j) (v ω (SW ω) j) ∩ Ico 0 t) +
              volume ({u ω (SW ω) j, fs ω j} : Set ℝ) := measure_union_le _ _
        _ = _ := by rw [hfin, add_zero]
    · exact measure_mono (inter_subset_inter_left _ hsub1)
  rw [hvol]
  have hu := u_pos h j
  have heq : Ioo (u ω (SW ω) j) (v ω (SW ω) j) ∩ Ico 0 t =
      Ioo (u ω (SW ω) j) (min (v ω (SW ω) j) t) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩
      exact ⟨⟨h1, h2⟩, by linarith, h4⟩
  rw [heq, Real.volume_Ioo, ENNReal.toReal_ofReal']

theorem served_lt_iff (h : Hyp ω (SW ω)) (j : ℕ) (t : ℝ) :
    served (sch SW) (0, j) ω t < x ω j ↔ t < v ω (SW ω) j := by
  rw [served_eq h, x_eq (SW := SW)]
  have hx := h.xpos j
  rw [x_eq (SW := SW)] at hx
  constructor
  · intro hlt
    by_contra hc
    push_neg at hc
    rw [min_eq_left hc] at hlt
    have := le_max_left (v ω (SW ω) j - u ω (SW ω) j) 0
    linarith
  · intro hlt
    rw [min_eq_right hlt.le]
    exact max_lt (by linarith) (by linarith)

theorem present_iff (h : Hyp ω (SW ω)) (j : ℕ) (t : ℝ) :
    present (sch SW) (0, j) ω t ↔ P ω (SW ω) j t := by
  unfold present P
  rw [← served_lt_iff h j t]
  rfl

theorem departure_eq (h : Hyp ω (SW ω)) (j : ℕ) :
    departure (sch SW) (0, j) ω = v ω (SW ω) j := by
  unfold departure
  have : {t : ℝ | serviceReq ω (0, j) ≤ served (sch SW) (0, j) ω t} = Ici (v ω (SW ω) j) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    have := served_lt_iff h j t
    have hs : serviceReq ω (0, j) = x ω j := rfl
    rw [hs]
    constructor
    · intro h1; by_contra h2; exact absurd (this.2 (not_le.1 h2)) (not_lt.2 h1)
    · intro h1; by_contra h2; exact absurd (this.1 (not_le.1 h2)) (not_lt.2 h1)
  rw [this, csInf_Ici]

theorem complete (h : Hyp ω (SW ω)) (j : ℕ) :
    ∃ t, serviceReq ω (0, j) ≤ served (sch SW) (0, j) ω t := by
  refine ⟨v ω (SW ω) j, ?_⟩
  by_contra hc
  exact lt_irrefl _ ((served_lt_iff h j _).1 (not_le.1 hc))

theorem c2 (h : Hyp ω (SW ω)) (t : ℝ) (k : Job 1) (hk : sch SW ω t = some k) :
    present (sch SW) k ω t := by
  rw [job1 k] at hk ⊢
  exact (present_iff h k.2 t).2 (mem_of_sch h hk).1

theorem c3 (h : Hyp ω (SW ω)) (t : ℝ) :
    sch SW ω t = none ↔ ∀ k : Job 1, ¬ present (sch SW) k ω t := by
  constructor
  · intro hn k hk
    rw [job1 k, present_iff h] at hk
    unfold sch at hn
    by_cases hW : ∃ m, Win ω (SW ω) m t
    · rw [dif_pos hW] at hn; simp at hn
    · rw [dif_neg hW, dif_pos ⟨k.2, hk⟩] at hn; simp at hn
  · intro hk
    have hP : ¬ ∃ j, P ω (SW ω) j t := fun ⟨j, hj⟩ => hk (0, j) ((present_iff h j t).2 hj)
    have hW : ¬ ∃ m, Win ω (SW ω) m t := fun ⟨m, hm⟩ => hP ⟨m + 1, win_P h hm⟩
    unfold sch
    rw [dif_neg hW, dif_neg hP]

theorem cL (h : Hyp ω (SW ω)) (t : ℝ) (q : Job 1) (δ : ℝ) (hδ : 0 < δ)
    (hq : ∀ s ∈ Ioo (t - δ) t, sch SW ω s = some q) (hp : present (sch SW) q ω t) :
    sch SW ω t = some q := by
  rw [job1 q] at hq hp ⊢
  have hP := (present_iff h q.2 t).1 hp
  have k1 := mem_of_sch h (hq (t - δ / 2) ⟨by linarith, by linarith⟩)
  have k2 := mem_of_sch h (hq (t - δ / 4) ⟨by linarith, by linarith⟩)
  have hut : u ω (SW ω) q.2 < t := by
    rcases k1.2 with h1 | h1
    · linarith
    · rcases k2.2 with h2 | h2
      · linarith
      · linarith
  exact sch_of_mem h hut hP.2

theorem cLow (h : Hyp ω (SW ω)) (t : ℝ)
    (hno : ¬ ∃ q : Job 1, ∃ δ > 0, (∀ s ∈ Ioo (t - δ) t, sch SW ω s = some q) ∧
      present (sch SW) q ω t)
    (j : Job 1) (hj : present (sch SW) j ω t)
    (hlow : ∀ k : Job 1, k.2 < j.2 → ¬ present (sch SW) k ω t) : sch SW ω t = some j := by
  have hW : ¬ ∃ m, Win ω (SW ω) m t := by
    rintro ⟨m, hm⟩
    apply hno
    refine ⟨(0, m + 1), t - fs ω m, by linarith [hm.2.1], ?_, (present_iff h _ t).2 (win_P h hm)⟩
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    exact sch_win h ⟨hm.1, by linarith, by linarith [hm.2.2]⟩
  rw [job1 j] at hj ⊢
  exact sch_low hW ((present_iff h j.2 t).1 hj)
    (fun i hi hPi => hlow (0, i) hi ((present_iff h i t).2 hPi))

/-- Lindley form of the FCFS start times. -/
theorem lindley (k : ℕ) : ∃ i ≤ k, fs ω k = a ω i + ∑ l ∈ Finset.Ico i k, x ω l := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simp [fs]⟩
  | succ k ih =>
    obtain ⟨i, hi, hk⟩ := ih
    rw [fs_succ]
    rcases le_total (d ω k) (a ω (k + 1)) with h1 | h1
    · exact ⟨k + 1, le_rfl, by rw [max_eq_left h1]; simp⟩
    · refine ⟨i, by omega, ?_⟩
      rw [max_eq_right h1, Finset.sum_Ico_succ_top hi]
      unfold d
      rw [hk]
      ring

theorem workIn_eq (h : Hyp ω (SW ω)) (i n : ℕ) :
    workIn ω (a ω i) (a ω n) = ∑ l ∈ Finset.Ico i n, x ω l := by
  unfold workIn
  have hsm := a_strictMono h
  let e : ℕ ↪ Job 1 := ⟨fun l => ((0 : Fin 1), l), fun l l' hl => congrArg Prod.snd hl⟩
  rw [tsum_eq_sum (s := (Finset.Ico i n).map e)]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Ico] at hl
    have hmem : ((0 : Fin 1), l) ∈ {j : Job 1 | a ω i ≤ arrival ω j ∧ arrival ω j < a ω n} :=
      ⟨hsm.monotone hl.1, hsm hl.2⟩
    show Set.indicator _ (serviceReq ω) ((0 : Fin 1), l) = x ω l
    rw [Set.indicator_of_mem hmem]
    rfl
  · intro j hj
    apply Set.indicator_of_notMem
    rintro ⟨h1, h2⟩
    apply hj
    rw [job1 j] at h1 h2 ⊢
    have h1' : i ≤ j.2 := hsm.le_iff_le.1 h1
    have h2' : j.2 < n := hsm.lt_iff_lt.1 h2
    exact Finset.mem_map_of_mem e (Finset.mem_Ico.2 ⟨h1', h2'⟩)

theorem bp_d (h : Hyp ω (SW ω)) (n : ℕ) (hbp : IsBPStart ω (0, n + 1)) :
    d ω n ≤ a ω (n + 1) := by
  obtain ⟨i, hi, hfs⟩ := lindley (ω := ω) n
  have hai : a ω i ≤ a ω (n + 1) := (a_strictMono h).monotone (by omega)
  have h1 := hbp (a ω i) hai
  have h2 : workIn ω (a ω i) (arrival ω (0, n + 1)) = ∑ l ∈ Finset.Ico i (n + 1), x ω l :=
    workIn_eq h i (n + 1)
  rw [h2, Finset.sum_Ico_succ_top (by omega)] at h1
  unfold d
  rw [hfs]
  have : arrival ω (0, n + 1) = a ω (n + 1) := rfl
  linarith

theorem hold (h : Hyp ω (SW ω)) (j0 : Job 1) (hbp : IsBPStart ω j0) (k : Job 1) (t : ℝ)
    (hk : k.2 < j0.2) (ht : arrival ω j0 ≤ t) : ¬ present (sch SW) k ω t := by
  rw [job1 k, present_iff h]
  rw [job1 j0] at hbp ht
  obtain ⟨n, hn⟩ : ∃ n, j0.2 = n + 1 := ⟨j0.2 - 1, by omega⟩
  rw [hn] at hbp ht hk
  have hbd := bp_d h n hbp
  have hfs : fs ω (n + 1) = a ω (n + 1) := by
    rw [fs_succ]; exact max_eq_left hbd
  rintro ⟨_, hv⟩
  by_cases hex : k.2 + 1 = n + 1 ∧ SW ω k.2
  · have hkn : k.2 = n := by omega
    have h1 := h.arr k.2 hex.2
    rw [hkn] at h1
    have h2 := fs_lt_d h n
    linarith
  · have := before_slot h hk hex
    have ht' : a ω (n + 1) ≤ t := ht
    linarith

theorem classOffset_eq (h : Hyp ω (SW ω)) (j0 : Job 1) : classOffset ω j0 0 = j0.2 := by
  unfold classOffset
  have : {m : ℕ | arrival ω ((0 : Fin 1), m) < arrival ω j0} = (Finset.range j0.2 : Set ℕ) := by
    ext m
    rw [job1 j0]
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    exact (a_strictMono h).lt_iff_lt
  rw [this, Set.ncard_coe_finset, Finset.card_range]

/-- Clause 5 pathwise for the swap schedule with the inertia rule. -/
theorem c5 (h : Hyp ω (SW ω)) (j0 : Job 1) (hbp : IsBPStart ω j0) (t : ℝ) (hin : InBP ω j0 t) :
    sch SW ω t = (CMI.irule (history (sch SW) ω j0 t) (seed ω j0)).map
      (fun p => (p.1, classOffset ω j0 p.1 + p.2)) := by
  refine CMI.clause5 j0 (classOffset_eq h j0) ?_ (c2 h) (hold h j0 hbp) (cL h) (cLow h)
    (fun t ht => (c3 h t).2 ht) t hin.1
  intro k hk
  rw [job1 j0, job1 k]
  exact (a_strictMono h).monotone hk

end

end CMX

/-! Part CMX (continued): measurability, the two swap predicates (FCFS and coin swap) and
`IsStrategy`. -/

namespace CMX
set_option linter.unusedSectionVars false

open CoffmanMitrani Set MeasureTheory

section
open Classical

theorem meas_x (k : ℕ) : Measurable fun ω : Omega 1 => x ω k :=
  (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)

theorem meas_τ (k : ℕ) : Measurable fun ω : Omega 1 => τ ω k :=
  (measurable_pi_apply _).comp measurable_fst

theorem meas_a (k : ℕ) : Measurable fun ω : Omega 1 => a ω k := by
  unfold a arrival
  exact Finset.measurable_sum _ fun m _ => (measurable_pi_apply _).comp measurable_fst

theorem meas_fs (k : ℕ) : Measurable fun ω : Omega 1 => fs ω k := by
  induction k with
  | zero => exact meas_a 0
  | succ k ih => exact (meas_a (k + 1)).max (ih.add (meas_x k))

theorem meas_d (k : ℕ) : Measurable fun ω : Omega 1 => d ω k := (meas_fs k).add (meas_x k)

variable {SW : Omega 1 → ℕ → Prop}

theorem meas_v (hSW : ∀ m, MeasurableSet {ω | SW ω m}) (k : ℕ) :
    Measurable fun ω => v ω (SW ω) k := by
  unfold v
  refine Measurable.ite (hSW k) (meas_d (k + 1))
    (Measurable.ite ?_ ((meas_fs (k - 1)).add (meas_x k)) (meas_d k))
  exact measurableSet_setOfPred.2
    (Measurable.exists fun m => measurable_const.and (measurableSet_setOfPred.1 (hSW m)))

theorem meas_Win (hSW : ∀ m, MeasurableSet {ω | SW ω m}) (m : ℕ) :
    Measurable fun p : Omega 1 × ℝ => Win p.1 (SW p.1) m p.2 :=
  ((measurableSet_setOfPred.1 (hSW m)).comp measurable_fst).and
    ((measurableSet_setOfPred.1 (measurableSet_lt ((meas_fs m).comp measurable_fst)
      measurable_snd)).and (measurableSet_setOfPred.1 (measurableSet_lt measurable_snd
      (((meas_fs m).add (meas_x (m + 1))).comp measurable_fst))))

theorem meas_P (hSW : ∀ m, MeasurableSet {ω | SW ω m}) (k : ℕ) :
    Measurable fun p : Omega 1 × ℝ => P p.1 (SW p.1) k p.2 :=
  (measurableSet_setOfPred.1 (measurableSet_le ((meas_a k).comp measurable_fst)
    measurable_snd)).and (measurableSet_setOfPred.1 (measurableSet_lt measurable_snd
    ((meas_v hSW k).comp measurable_fst)))

theorem sch_some_iff (ω : Omega 1) (t : ℝ) (n : ℕ) :
    sch SW ω t = some (0, n) ↔
      ((∃ m, Win ω (SW ω) m t) ∧ 1 ≤ n ∧ Win ω (SW ω) (n - 1) t ∧
          ∀ m, m < n - 1 → ¬ Win ω (SW ω) m t) ∨
        ((¬ ∃ m, Win ω (SW ω) m t) ∧ P ω (SW ω) n t ∧ ∀ i, i < n → ¬ P ω (SW ω) i t) := by
  unfold sch
  by_cases hW : ∃ m, Win ω (SW ω) m t
  · rw [dif_pos hW]
    constructor
    · intro he
      have he' : Nat.find hW + 1 = n := by
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        exact he.2
      have h1 := Nat.find_spec hW
      refine Or.inl ⟨hW, by omega, ?_, ?_⟩
      · rw [show n - 1 = Nat.find hW by omega]; exact h1
      · intro m hm; exact Nat.find_min hW (by omega)
    · rintro (⟨_, h1, h2, h3⟩ | ⟨h1, _⟩)
      · have := (Nat.find_eq_iff hW).2 ⟨h2, h3⟩
        rw [this, show n - 1 + 1 = n by omega]
      · exact absurd hW h1
  · rw [dif_neg hW]
    by_cases hP : ∃ i, P ω (SW ω) i t
    · rw [dif_pos hP]
      constructor
      · intro he
        have he' : Nat.find hP = n := by
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          exact he.2
        rw [← he']
        exact Or.inr ⟨hW, Nat.find_spec hP, fun i hi => Nat.find_min hP hi⟩
      · rintro (⟨h1, _⟩ | ⟨_, h1, h2⟩)
        · exact absurd h1 hW
        · rw [(Nat.find_eq_iff hP).2 ⟨h1, h2⟩]
    · rw [dif_neg hP]
      constructor
      · intro he; simp at he
      · rintro (⟨h1, _⟩ | ⟨_, h1, _⟩)
        · exact absurd h1 hW
        · exact absurd ⟨n, h1⟩ hP

theorem meas_sch (hSW : ∀ m, MeasurableSet {ω | SW ω m}) (k : Job 1) :
    MeasurableSet {p : Omega 1 × ℝ | sch SW p.1 p.2 = some k} := by
  rw [job1 k]
  apply measurableSet_setOfPred.2
  have e := funext fun p : Omega 1 × ℝ => propext (sch_some_iff (SW := SW) p.1 p.2 k.2)
  rw [e]
  exact ((Measurable.exists fun m => meas_Win hSW m).and (measurable_const.and
    ((meas_Win hSW (k.2 - 1)).and (Measurable.forall fun m =>
      measurable_const.imp (meas_Win hSW m).not)))).or
    ((Measurable.exists fun m => meas_Win hSW m).not.and ((meas_P hSW k.2).and
      (Measurable.forall fun i => measurable_const.imp (meas_P hSW i).not)))

theorem isStrategy_sch (hSW : ∀ m, MeasurableSet {ω | SW ω m})
    (hae : ∀ᵐ ω ∂CMDP.D1.P, Hyp ω (SW ω)) : IsStrategy CMDP.D1 (sch SW) := by
  refine ⟨fun j => (meas_sch hSW j).nullMeasurableSet, CMI.irule, ?_⟩
  filter_upwards [hae] with ω h
  exact ⟨c2 h, fun t => c3 h t, fun j => by rw [job1 j]; exact complete h j.2,
    fun j0 t hbp hin => c5 h j0 hbp t hin⟩

end

/-- FCFS: no swaps. -/
def SW0 : Omega 1 → ℕ → Prop := fun _ _ => False

/-- The threshold swap: job `m + 1` (short, `x ≤ 1`) jumps ahead of job `m` (long, `x > 2`) when
job `m - 1` was long and the two interarrival times are at most `1`, so job `m + 1` has surely
arrived when job `m` would start. Consecutive swaps are impossible (`x (m+1) ≤ 1 < 2`). -/
def SW1 : Omega 1 → ℕ → Prop := fun ω m =>
  1 ≤ m ∧ x ω (m + 1) ≤ 1 ∧ 2 < x ω m ∧ 2 < x ω (m - 1) ∧ τ ω m ≤ 1 ∧ τ ω (m + 1) ≤ 1

theorem hyp0 {ω : Omega 1} (hτ : ∀ k, 0 < τ ω k) (hx : ∀ k, 0 < x ω k) : Hyp ω (SW0 ω) :=
  ⟨hτ, hx, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem hyp1 {ω : Omega 1} (hτ : ∀ k, 0 < τ ω k) (hx : ∀ k, 0 < x ω k) : Hyp ω (SW1 ω) := by
  refine ⟨hτ, hx, ?_, fun m h => by linarith [h.2.1, h.2.2.1], fun m h h' => by
    linarith [h.2.1, h'.2.2.1]⟩
  intro m hm
  obtain ⟨h1, _, _, h4, h5, h6⟩ := hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 := a_succ (ω := ω) (k + 1)
  have e2 := a_succ (ω := ω) k
  have e3 := a_le_fs (ω := ω) k
  have e4 := d_le_fs_succ (ω := ω) k
  simp only [Nat.add_sub_cancel] at h4
  unfold d at e4
  linarith

theorem meas_SW0 (m : ℕ) : MeasurableSet {ω | SW0 ω m} := by
  simp [SW0]

theorem meas_SW1 (m : ℕ) : MeasurableSet {ω | SW1 ω m} := by
  apply measurableSet_setOfPred.2
  exact measurable_const.and
    ((measurableSet_setOfPred.1 (measurableSet_le (meas_x (m + 1)) measurable_const)).and
    ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const (meas_x m))).and
    ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const (meas_x (m - 1)))).and
    ((measurableSet_setOfPred.1 (measurableSet_le (meas_τ m) measurable_const)).and
    (measurableSet_setOfPred.1 (measurableSet_le (meas_τ (m + 1)) measurable_const))))))

/-- FCFS serves the lowest-index present job (the priority clause, pathwise). -/
theorem pr0 {ω : Omega 1} (t : ℝ) (j j' : Job 1) (hj : sch SW0 ω t = some j)
    (hj' : present (sch SW0) j' ω t) (h : Hyp ω (SW0 ω)) : j.2 ≤ j'.2 := by
  rw [job1 j] at hj
  rw [job1 j', present_iff h] at hj'
  rcases (sch_some_iff ω t j.2).1 hj with ⟨⟨m, hm⟩, _⟩ | ⟨_, _, h3⟩
  · exact hm.1.elim
  · by_contra hc
    exact h3 j'.2 (not_le.1 hc) hj'

end CMX

/-! P3 of the theorem_2 disproof: the threshold-swap schedule achieves `P0 + c` with `c < 0`. -/

namespace CMY
set_option linter.unusedSectionVars false

open CoffmanMitrani MeasureTheory ProbabilityTheory Set CMX

/-- Integral of a finite product of coordinate functions under an infinite product measure. -/
theorem IP {ι : Type*} [DecidableEq ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (F : ι → ℝ → ℝ) (hF : ∀ i, Measurable (F i)) :
    ∫ y, ∏ i ∈ s, F i (y i) ∂(Measure.infinitePi μ) = ∏ i ∈ s, ∫ x, F i x ∂(μ i) := by
  have h1 : (fun y : ι → ℝ => ∏ i ∈ s, F i (y i)) =
      fun y => (fun z : s → ℝ => ∏ i : s, F i (z i)) (s.restrict y) := by
    funext y
    exact (Finset.prod_coe_sort s (fun i => F i (y i))).symm
  rw [h1]
  refine (integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun z : s → ℝ => ∏ i : s, F i (z i)) ?hf).trans ?main
  case hf =>
    have hm : Measurable (fun z : s → ℝ => ∏ i : s, F i (z i)) :=
      Finset.measurable_prod _ (fun i _ => (hF i).comp (measurable_pi_apply i))
    exact hm.aestronglyMeasurable
  case main =>
    rw [integral_fintype_prod_eq_prod (fun i : s => F i)]
    exact Finset.prod_coe_sort s (fun i => ∫ x, F i x ∂μ i)

theorem int2 {ι : Type*} [DecidableEq ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {i j : ι} (hij : i ≠ j) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ∫ y, f (y i) * g (y j) ∂(Measure.infinitePi μ) = (∫ x, f x ∂(μ i)) * (∫ x, g x ∂(μ j)) := by
  classical
  let F : ι → ℝ → ℝ := fun l => if l = i then f else g
  have hF : ∀ l, Measurable (F l) := fun l => by
    simp only [F]; split_ifs; exacts [hf, hg]
  have := IP μ {i, j} F hF
  simpa [F, hij.symm, Finset.prod_pair hij] using this

theorem int3 {ι : Type*} [DecidableEq ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f g h : ℝ → ℝ) (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) :
    ∫ y, f (y i) * g (y j) * h (y k) ∂(Measure.infinitePi μ) =
      (∫ x, f x ∂(μ i)) * (∫ x, g x ∂(μ j)) * (∫ x, h x ∂(μ k)) := by
  classical
  let F : ι → ℝ → ℝ := fun l => if l = i then f else if l = j then g else h
  have hF : ∀ l, Measurable (F l) := fun l => by
    simp only [F]; split_ifs; exacts [hf, hg, hh]
  have := IP μ {i, j, k} F hF
  have hni : i ∉ ({j, k} : Finset ι) := by simp [hij, hik]
  simpa [F, hij.symm, hik.symm, hjk.symm, Finset.prod_insert hni, Finset.prod_pair hjk,
    mul_assoc] using this

/-- `D1.P` splits into the interarrival and the requirement coordinates. -/
theorem int_split (A B : (Job 1 → ℝ) → ℝ) :
    ∫ ω, A ω.1 * B ω.2.1 ∂CMDP.D1.P =
      (∫ y, A y ∂(Measure.infinitePi fun _ : Job 1 => expMeasure (1 : ℝ))) *
        (∫ y, B y ∂(Measure.infinitePi fun _ : Job 1 => expMeasure (2 : ℝ))) := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure one_pos
  haveI : IsProbabilityMeasure (expMeasure (2 : ℝ)) := isProbabilityMeasure_expMeasure two_pos
  show ∫ ω, A ω.1 * B ω.2.1 ∂((Measure.infinitePi fun _ : Job 1 => expMeasure (1 : ℝ)).prod
      ((Measure.infinitePi fun _ : Job 1 => expMeasure (2 : ℝ)).prod
      (Measure.infinitePi fun _ : Job 1 =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))) = _
  refine (integral_prod_mul A (fun q : (Job 1 → ℝ) × (Job 1 → ℕ → unitInterval) => B q.1)).trans ?_
  congr 1
  rw [integral_fun_fst B, probReal_univ, one_smul]

/-- the five one-dimensional constants -/
noncomputable def p1 : ℝ := ∫ t, (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) t ∂(expMeasure (1 : ℝ))
noncomputable def r1 : ℝ := ∫ t, (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) t ∂(expMeasure (2 : ℝ))
noncomputable def q2 : ℝ := ∫ t, (Ioi (2 : ℝ)).indicator (1 : ℝ → ℝ) t ∂(expMeasure (2 : ℝ))
noncomputable def e1 : ℝ := ∫ t, (Iic (1 : ℝ)).indicator id t ∂(expMeasure (2 : ℝ))
noncomputable def e2 : ℝ := ∫ t, (Ioi (2 : ℝ)).indicator id t ∂(expMeasure (2 : ℝ))

/-- the response-time shift -/
noncomputable def cc : ℝ := p1 * p1 * (e1 * q2 * q2) - p1 * p1 * (e2 * r1 * q2)

theorem cdf_pos {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    0 < ∫ t, (Iic c).indicator (1 : ℝ → ℝ) t ∂(expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [integral_indicator_one measurableSet_Iic, ← cdf_eq_real, cdf_expMeasure_eq hr,
    if_pos hc.le]
  have : Real.exp (-(r * c)) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
  rw [Real.exp_zero] at this
  linarith

theorem tail_pos {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    0 < ∫ t, (Ioi c).indicator (1 : ℝ → ℝ) t ∂(expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [integral_indicator_one measurableSet_Ioi]
  have h1 := measureReal_add_measureReal_compl (μ := expMeasure r) (s := Iic c)
    measurableSet_Iic
  rw [compl_Iic, probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hc.le] at h1
  have : 0 < Real.exp (-(r * c)) := Real.exp_pos _
  linarith

theorem cc_neg (hint : Integrable id (expMeasure (2 : ℝ))) : cc < 0 := by
  have hp : 0 < p1 := cdf_pos one_pos one_pos
  have hr : 0 < r1 := cdf_pos two_pos one_pos
  have hq : 0 < q2 := tail_pos two_pos two_pos
  haveI := isProbabilityMeasure_expMeasure (two_pos : (0 : ℝ) < 2)
  have he1 : e1 ≤ r1 := by
    apply integral_mono (hint.indicator measurableSet_Iic)
      ((integrable_const 1).indicator measurableSet_Iic)
    intro t
    by_cases ht : t ∈ Iic (1 : ℝ)
    · simp only [Set.indicator_of_mem ht, id, Pi.one_apply]; exact ht
    · simp only [Set.indicator_of_notMem ht, le_refl]
  have he2 : 2 * q2 ≤ e2 := by
    rw [q2, ← integral_const_mul]
    apply integral_mono (((integrable_const 1).indicator measurableSet_Ioi).const_mul 2)
      (hint.indicator measurableSet_Ioi)
    intro t
    by_cases ht : t ∈ Ioi (2 : ℝ)
    · simp only [Set.indicator_of_mem ht, id, Pi.one_apply, mul_one]; exact le_of_lt ht
    · simp only [Set.indicator_of_notMem ht, mul_zero, le_refl]
  have hp2 : 0 < p1 * p1 * q2 := by positivity
  have : cc = p1 * p1 * q2 * (e1 * q2 - e2 * r1) := by unfold cc; ring
  rw [this]
  apply mul_neg_of_pos_of_neg hp2
  nlinarith

end CMY

namespace CMX
set_option linter.unusedSectionVars false
open CoffmanMitrani Set

open Classical in
theorem v_formula {SW : Omega 1 → ℕ → Prop} {ω : Omega 1} (h : Hyp ω (SW ω)) (n : ℕ) :
    v ω (SW ω) n = d ω n + (if SW ω n then x ω (n + 1) else 0) -
      (if (∃ m, n = m + 1 ∧ SW ω m) then x ω (n - 1) else 0) := by
  by_cases hA : SW ω n
  · have hB : ¬ ∃ m, n = m + 1 ∧ SW ω m := by
      rintro ⟨m, rfl, hm⟩; exact h.nn m hm hA
    rw [v_A h hA, if_pos hA, if_neg hB]
    unfold d; rw [fs_succ_sw h hA]; unfold d; ring
  · by_cases hB : ∃ m, n = m + 1 ∧ SW ω m
    · rw [if_neg hA, if_pos hB]
      obtain ⟨m, rfl, hm⟩ := hB
      rw [v_B h hm]
      unfold d; rw [fs_succ_sw h hm]; unfold d
      simp only [Nat.add_sub_cancel]; ring
    · rw [v_C h hA hB, if_neg hA, if_neg hB]; ring

theorem resp_eq {SW : Omega 1 → ℕ → Prop} {ω : Omega 1} (h : Hyp ω (SW ω)) (n : ℕ) :
    responseTime (sch SW) (0, n) ω = v ω (SW ω) n - a ω n := by
  unfold responseTime
  rw [departure_eq h]
  rfl

end CMX

namespace CMY
set_option linter.unusedSectionVars false
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CMX

noncomputable def A1 (k : ℕ) (y : Job 1 → ℝ) : ℝ :=
  (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 2)) * (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 3))
noncomputable def B1 (k : ℕ) (y : Job 1 → ℝ) : ℝ :=
  (Iic (1 : ℝ)).indicator id (y (0, k + 3)) * (Ioi (2 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 2)) *
    (Ioi (2 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 1))
noncomputable def A2 (k : ℕ) (y : Job 1 → ℝ) : ℝ :=
  (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 1)) * (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 2))
noncomputable def B2 (k : ℕ) (y : Job 1 → ℝ) : ℝ :=
  (Ioi (2 : ℝ)).indicator id (y (0, k + 1)) * (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k + 2)) *
    (Ioi (2 : ℝ)).indicator (1 : ℝ → ℝ) (y (0, k))

open Classical in
theorem T1_eq (k : ℕ) (ω : Omega 1) :
    (if SW1 ω (k + 2) then x ω (k + 2 + 1) else 0) = A1 k ω.1 * B1 k ω.2.1 := by
  have e : k + 2 - 1 = k + 1 := by omega
  have e3 : k + 2 + 1 = k + 3 := rfl
  simp only [SW1, A1, B1, e, e3, Set.indicator_apply, Set.mem_Iic, Set.mem_Ioi, Pi.one_apply, id, x, τ,
    ite_and]
  split_ifs <;> first | (exfalso; omega) | ring1

open Classical in
theorem T2_eq (k : ℕ) (ω : Omega 1) :
    (if (∃ m, k + 2 = m + 1 ∧ SW1 ω m) then x ω (k + 2 - 1) else 0) = A2 k ω.1 * B2 k ω.2.1 := by
  have e1 : (∃ m, k + 2 = m + 1 ∧ SW1 ω m) ↔ SW1 ω (k + 1) :=
    ⟨fun ⟨m, hm, h⟩ => by rw [show m = k + 1 by omega] at h; exact h, fun h => ⟨k + 1, rfl, h⟩⟩
  rw [if_congr e1 rfl rfl]
  have e : k + 2 - 1 = k + 1 := by omega
  have e' : k + 1 - 1 = k := by omega
  have e2 : k + 1 + 1 = k + 2 := rfl
  simp only [SW1, A2, B2, e, e', e2, Set.indicator_apply, Set.mem_Iic, Set.mem_Ioi, Pi.one_apply, id, x,
    τ, ite_and]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem mI {s : Set ℝ} (hs : MeasurableSet s) : Measurable (s.indicator (1 : ℝ → ℝ)) :=
  measurable_const.indicator hs
theorem mJ {s : Set ℝ} (hs : MeasurableSet s) : Measurable (s.indicator (id : ℝ → ℝ)) :=
  measurable_id.indicator hs

theorem ET1 (k : ℕ) : ∫ ω, A1 k ω.1 * B1 k ω.2.1 ∂CMDP.D1.P = p1 * p1 * (e1 * q2 * q2) := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure one_pos
  haveI : IsProbabilityMeasure (expMeasure (2 : ℝ)) := isProbabilityMeasure_expMeasure two_pos
  rw [int_split]
  congr 1
  · exact int2 (fun _ : Job 1 => expMeasure (1 : ℝ)) (i := (0, k + 2)) (j := (0, k + 3))
      (by simp) _ _ (mI measurableSet_Iic) (mI measurableSet_Iic)
  · exact int3 (fun _ : Job 1 => expMeasure (2 : ℝ)) (i := (0, k + 3)) (j := (0, k + 2))
      (k := (0, k + 1)) (by simp) (by simp) (by simp) _ _ _ (mJ measurableSet_Iic)
      (mI measurableSet_Ioi) (mI measurableSet_Ioi)

theorem ET2 (k : ℕ) : ∫ ω, A2 k ω.1 * B2 k ω.2.1 ∂CMDP.D1.P = p1 * p1 * (e2 * r1 * q2) := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure one_pos
  haveI : IsProbabilityMeasure (expMeasure (2 : ℝ)) := isProbabilityMeasure_expMeasure two_pos
  rw [int_split]
  congr 1
  · exact int2 (fun _ : Job 1 => expMeasure (1 : ℝ)) (i := (0, k + 1)) (j := (0, k + 2))
      (by simp) _ _ (mI measurableSet_Iic) (mI measurableSet_Iic)
  · exact int3 (fun _ : Job 1 => expMeasure (2 : ℝ)) (i := (0, k + 1)) (j := (0, k + 2))
      (k := (0, k)) (by simp) (by simp) (by simp) _ _ _ (mJ measurableSet_Ioi)
      (mI measurableSet_Iic) (mI measurableSet_Ioi)

end CMY

namespace CMY
set_option linter.unusedSectionVars false
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CMX

theorem intx (hint : Integrable id (expMeasure (2 : ℝ))) (k : ℕ) :
    Integrable (fun ω : Omega 1 => x ω k) CMDP.D1.P := by
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure one_pos
  haveI : IsProbabilityMeasure (expMeasure (2 : ℝ)) := isProbabilityMeasure_expMeasure two_pos
  have mp : MeasurePreserving (fun ω : Omega 1 => ω.2.1 (0, k))
      ((Measure.infinitePi fun _ : Job 1 => expMeasure (1 : ℝ)).prod
      ((Measure.infinitePi fun _ : Job 1 => expMeasure (2 : ℝ)).prod
      (Measure.infinitePi fun _ : Job 1 =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))) (expMeasure 2) :=
    (measurePreserving_eval_infinitePi (fun _ : Job 1 => expMeasure (2 : ℝ)) (0, k)).comp
      (measurePreserving_fst.comp measurePreserving_snd)
  exact (mp.integrable_comp hint.aestronglyMeasurable).2 hint

open Classical in
theorem achieves_S1 (hint : Integrable id (expMeasure (2 : ℝ))) (Lib : Schedule 1)
    (P0 : Fin CMDP.D1.M → ℝ) (hLs : IsStrategy CMDP.D1 Lib) (hLp : IsPriority CMDP.D1 1 Lib)
    (hA : Achieves CMDP.D1 Lib P0)
    (hpos : ∀ᵐ ω ∂CMDP.D1.P, (∀ j, 0 < ω.1 j) ∧ (∀ j, 0 < ω.2.1 j)) :
    Achieves CMDP.D1 (sch SW1) (fun i => P0 i + cc) := by
  have hH : ∀ᵐ ω ∂CMDP.D1.P, Hyp ω (SW0 ω) ∧ Hyp ω (SW1 ω) := by
    filter_upwards [hpos] with ω h
    exact ⟨hyp0 (fun k => h.1 _) (fun k => h.2 _), hyp1 (fun k => h.1 _) (fun k => h.2 _)⟩
  obtain ⟨ruleL, hL⟩ := hLs.2
  have fin1' : ∀ a b : Fin CMDP.D1.M, a = b := fun a b =>
    Fin.ext (by have ha := a.2; have hb := b.2; simp only [CMDP.D1] at ha hb; omega)
  have hpin : ∀ᵐ ω ∂CMDP.D1.P, ∀ n : ℕ,
      responseTime (sch SW0) (0, n) ω = responseTime Lib (0, n) ω := by
    filter_upwards [hH, hL, hLp] with ω hh hl hp
    have prL : ∀ (t : ℝ) (j j' : Job 1), Lib ω t = some j → present Lib j' ω t → j.2 ≤ j'.2 := by
      intro t j j' h1 h2
      rcases hp t j j' h1 h2 with h | h
      · exact absurd h (by
          rw [fin1' ((1 : Equiv.Perm (Fin CMDP.D1.M)).symm j.1)
            ((1 : Equiv.Perm (Fin CMDP.D1.M)).symm j'.1)]
          exact lt_irrefl _)
      · exact h.2
    intro n
    exact CMP.responseTime_pin (CMP.served_pin (c2 hh.1) (c3 hh.1)
      (fun t j j' h1 h2 => pr0 t j j' h1 h2 hh.1) hl.1 hl.2.1 prL) (0, n)
  have hrel : ∀ᵐ ω ∂CMDP.D1.P, ∀ n : ℕ, responseTime (sch SW1) (0, n) ω =
      responseTime (sch SW0) (0, n) ω + ((if SW1 ω n then x ω (n + 1) else 0) -
        (if (∃ m, n = m + 1 ∧ SW1 ω m) then x ω (n - 1) else 0)) := by
    filter_upwards [hH] with ω hh
    intro n
    have e0 : v ω (SW0 ω) n = d ω n := by
      rw [v_formula hh.1]; simp [SW0]
    rw [resp_eq hh.2, resp_eq hh.1, v_formula hh.2, e0]
    ring
  have hI1 : ∀ n, Integrable (fun ω => if SW1 ω n then x ω (n + 1) else 0) CMDP.D1.P := by
    intro n
    refine ((intx hint (n + 1)).indicator (meas_SW1 n)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hI2 : ∀ n, Integrable (fun ω => if (∃ m, n = m + 1 ∧ SW1 ω m) then x ω (n - 1) else 0)
      CMDP.D1.P := by
    intro n
    have hs : MeasurableSet {ω : Omega 1 | ∃ m, n = m + 1 ∧ SW1 ω m} :=
      measurableSet_setOfPred.2 (Measurable.exists fun m =>
        measurable_const.and (measurableSet_setOfPred.1 (meas_SW1 m)))
    refine ((intx hint (n - 1)).indicator hs).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  intro i
  have hj : ∀ n : ℕ, ((i, n) : Job 1) = ((0 : Fin 1), n) := fun n => Prod.ext (CMI.fin1 _) rfl
  obtain ⟨hA1, hA2⟩ := hA i
  simp only [hj] at hA1 hA2 ⊢
  have hint0 : ∀ n, Integrable (fun ω => responseTime (sch SW0) (0, n) ω) CMDP.D1.P :=
    fun n => (hA1 n).congr (hpin.mono fun ω h => (h n).symm)
  refine ⟨fun n => ?_, ?_⟩
  · refine ((hint0 n).add ((hI1 n).sub (hI2 n))).congr ?_
    filter_upwards [hrel] with ω h
    exact (h n).symm
  · have hE : ∀ k : ℕ, ∫ ω, responseTime (sch SW1) (0, k + 2) ω ∂CMDP.D1.P =
        ∫ ω, responseTime Lib (0, k + 2) ω ∂CMDP.D1.P + cc := by
      intro k
      have hI12 : Integrable (fun ω => (if SW1 ω (k + 2) then x ω (k + 2 + 1) else 0) -
          (if (∃ m, k + 2 = m + 1 ∧ SW1 ω m) then x ω (k + 2 - 1) else 0)) CMDP.D1.P :=
        (hI1 _).sub (hI2 _)
      rw [integral_congr_ae (hrel.mono fun ω h => h (k + 2)),
        integral_add (hint0 _) hI12, integral_sub (hI1 _) (hI2 _),
        integral_congr_ae (hpin.mono fun ω h => h (k + 2))]
      have t1 : ∫ ω, (if SW1 ω (k + 2) then x ω (k + 2 + 1) else 0) ∂CMDP.D1.P =
          p1 * p1 * (e1 * q2 * q2) := by
        rw [← ET1 k]; congr 1; funext ω; exact T1_eq k ω
      have t2 : ∫ ω, (if (∃ m, k + 2 = m + 1 ∧ SW1 ω m) then x ω (k + 2 - 1) else 0)
          ∂CMDP.D1.P = p1 * p1 * (e2 * r1 * q2) := by
        rw [← ET2 k]; congr 1; funext ω; exact T2_eq k ω
      rw [t1, t2]
      unfold cc
      ring
    refine (hA2.add_const cc).congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact (hE k).symm

end CMY

open CoffmanMitrani in
/-- `CoffmanMitrani.theorem_2` is false as formalized: for one class (`λ = 1`, `μ = 2`) every
priority strategy achieves the FCFS vector `P0`, so `H D1 ⊆ {P0}`, while the anticipating
threshold-swap schedule (admissible through the inertia decision rule) achieves `P0 + cc` with
`cc < 0`. -/
theorem solution : ¬ (∀ (D : Data) (W : Fin D.M → ℝ), Achievable D W ↔ W ∈ H D) := by
  obtain ⟨P0, hA⟩ := CMB.achieves_schedule CMDP.D1 1
  have hLs := CMB.isStrategy_schedule CMDP.D1 1
  have hLp := CMB.isPriority_schedule CMDP.D1 1
  have hpos := CMB.ae_pos CMDP.D1
  have hint := (CMS.expMeasure_mean (two_pos : (0 : ℝ) < 2)).1
  have hae1 : ∀ᵐ ω ∂CMDP.D1.P, CMX.Hyp ω (CMX.SW1 ω) := by
    filter_upwards [hpos] with ω h
    exact CMX.hyp1 (fun k => h.1 _) (fun k => h.2 _)
  refine dp_conditional P0 (fun i => P0 i + CMY.cc) ?_
    ⟨CMX.sch CMX.SW1, CMX.isStrategy_sch CMX.meas_SW1 hae1,
      CMY.achieves_S1 hint (CMB.schedule 1) P0 hLs hLp hA hpos⟩ ?_
  · intro σ S Pv h1 h2 h3
    exact CMDP.pin_vec σ 1 S (CMB.schedule 1) Pv P0 h1 h2 h3 hLp hLs hA
  · intro h
    have h0 : P0 0 + CMY.cc = P0 0 := congrFun h 0
    have hc := CMY.cc_neg hint
    linarith
