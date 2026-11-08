-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.skorokhod_problem_1d
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:15:13.733947+00:00
-- url     : https://prove2.me/submissions/44359872-09b1-49e1-b1c8-ce2746594b1a

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory Filter Topology Set

namespace BWSkorokhodAux

open BellWilliams2001.ThresholdPolicy

/-- A Skorokhod path is bounded on every compact interval `[0, t]`. -/
lemma cadlag_bdd {x : ℝ → ℝ} (hx : IsCadlag x) (t : ℝ) :
    ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) t, |x z| ≤ C := by
  have key := (isCompact_Icc (a := (0 : ℝ)) (b := t)).induction_on
    (p := fun U => ∃ C : ℝ, ∀ z ∈ U, |x z| ≤ C)
    ⟨0, fun z hz => hz.elim⟩
    (fun s u hsu ⟨C, hC⟩ => ⟨C, fun z hz => hC z (hsu hz)⟩)
    (fun s u ⟨C, hC⟩ ⟨D, hD⟩ => ⟨max C D, fun z hz => by
      rcases hz with hz | hz
      · exact (hC z hz).trans (le_max_left _ _)
      · exact (hD z hz).trans (le_max_right _ _)⟩)
    (by
      intro y hy
      have hR : ∀ᶠ z in 𝓝[≥] y, |x z - x y| < 1 := by
        have := (hx.1 y hy.1)
        have h2 := Metric.tendsto_nhds.1 this 1 one_pos
        simpa [Real.dist_eq] using h2
      rcases eq_or_lt_of_le hy.1 with h0 | hpos
      · subst h0
        refine ⟨{z | |x z - x 0| < 1}, ?_, |x 0| + 1, ?_⟩
        · exact nhdsWithin_mono _ (fun z hz => hz.1) hR
        · intro z hz
          have := abs_sub_abs_le_abs_sub (x z) (x 0)
          simp only [mem_setOf_eq] at hz
          linarith
      · obtain ⟨l, hl⟩ := hx.2 y hpos
        have hL : ∀ᶠ z in 𝓝[<] y, |x z - l| < 1 := by
          have h2 := Metric.tendsto_nhds.1 hl 1 one_pos
          simpa [Real.dist_eq] using h2
        refine ⟨{z | |x z - x y| < 1 ∨ |x z - l| < 1}, ?_, max (|x y| + 1) (|l| + 1), ?_⟩
        · apply mem_nhdsWithin_of_mem_nhds
          rw [← nhdsLT_sup_nhdsGE]
          exact ⟨hL.mono fun z hz => Or.inr hz, hR.mono fun z hz => Or.inl hz⟩
        · intro z hz
          rcases hz with hz | hz
          · have := abs_sub_abs_le_abs_sub (x z) (x y)
            exact le_max_of_le_left (by linarith)
          · have := abs_sub_abs_le_abs_sub (x z) l
            exact le_max_of_le_right (by linarith))
  exact key

lemma cadlag_bddBelow {x : ℝ → ℝ} (hx : IsCadlag x) (t : ℝ) :
    BddBelow (Set.range fun s : Icc (0 : ℝ) t => x s) := by
  obtain ⟨C, hC⟩ := cadlag_bdd hx t
  refine ⟨-C, ?_⟩
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  have := hC s hs
  have := neg_abs_le (x s)
  simp only
  linarith

/-- A set each of whose points `s` admits `u > s` with `μ [s,u] = 0` is `μ`-null. -/
lemma null_of_right_null (μ : Measure ℝ) (E : Set ℝ)
    (h : ∀ s ∈ E, ∃ u, s < u ∧ μ (Icc s u) = 0) : μ E = 0 := by
  choose! u hu1 hu2 using h
  obtain ⟨T, hTE, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable E
    (fun s => Ioo s (u s)) (fun _ _ => isOpen_Ioo)
  set R := {s ∈ E | ∀ s' ∈ E, s ∉ Ioo s' (u s')} with hR
  have hRc : R.Countable := by
    apply Set.PairwiseDisjoint.countable_of_Ioo (y := u)
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro z hza hzb
      rcases lt_or_gt_of_ne hab with h | h
      · exact hb.2 a ha.1 ⟨h, lt_trans hzb.1 hza.2⟩
      · exact ha.2 b hb.1 ⟨h, lt_trans hza.1 hzb.2⟩
    · intro s hs
      exact hu1 s hs.1
  have hsub : E ⊆ ⋃ s ∈ T ∪ R, Icc s (u s) := by
    intro s hs
    by_cases hsR : s ∈ R
    · exact mem_biUnion (Or.inr hsR) ⟨le_rfl, (hu1 s hs).le⟩
    · have : ∃ s' ∈ E, s ∈ Ioo s' (u s') := by
        by_contra hne
        push_neg at hne
        exact hsR ⟨hs, hne⟩
      obtain ⟨s', hs'E, hs'⟩ := this
      have hmem : s ∈ ⋃ i ∈ E, Ioo i (u i) := mem_biUnion hs'E hs'
      rw [← hTU] at hmem
      obtain ⟨i, hiT, hi⟩ := mem_iUnion₂.1 hmem
      exact mem_biUnion (Or.inl hiT) (Ioo_subset_Icc_self hi)
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff (hTc.union hRc)]
  intro s hs
  rcases hs with hs | hs
  · exact hu2 s (hTE hs)
  · exact hu2 s hs.1


/-- The running infimum `inf_{0 ≤ s ≤ t} x(s)`. -/
noncomputable def rinf (x : ℝ → ℝ) (t : ℝ) : ℝ := ⨅ s : Icc (0 : ℝ) t, x s

lemma rinf_le {x : ℝ → ℝ} (hx : IsCadlag x) {z t : ℝ} (hz : z ∈ Icc (0 : ℝ) t) :
    rinf x t ≤ x z :=
  ciInf_le (cadlag_bddBelow hx t) ⟨z, hz⟩

lemma le_rinf {x : ℝ → ℝ} {c t : ℝ} (ht : 0 ≤ t) (h : ∀ z ∈ Icc (0 : ℝ) t, c ≤ x z) :
    c ≤ rinf x t := by
  haveI : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  exact le_ciInf fun z => h z z.2

lemma rinf_neg {x : ℝ → ℝ} {t : ℝ} (ht : t < 0) : rinf x t = 0 := by
  haveI : IsEmpty (Icc (0 : ℝ) t) := ⟨fun z => by linarith [z.2.1, z.2.2]⟩
  exact Real.iInf_of_isEmpty _

lemma rinf_zero {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) : rinf x 0 = 0 := by
  apply le_antisymm
  · exact (rinf_le hx ⟨le_rfl, le_rfl⟩).trans hx0.le
  · apply le_rinf le_rfl
    intro z hz
    have : z = 0 := le_antisymm hz.2 hz.1
    rw [this, hx0]

lemma rinf_nonpos {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) (t : ℝ) : rinf x t ≤ 0 := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [rinf_neg ht]
  · exact (rinf_le hx ⟨le_rfl, ht⟩).trans hx0.le

lemma vstar_mono {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) :
    Monotone (fun t => -rinf x t) := by
  intro s t hst
  simp only [neg_le_neg_iff]
  rcases lt_or_ge s 0 with hs | hs
  · rw [rinf_neg hs]; exact rinf_nonpos hx hx0 t
  · exact le_rinf hs fun z hz => rinf_le hx ⟨hz.1, hz.2.trans hst⟩

lemma vstar_rc {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) (t : ℝ) :
    ContinuousWithinAt (fun t => -rinf x t) (Ici t) t := by
  rcases lt_or_ge t 0 with ht | ht
  · apply ContinuousAt.continuousWithinAt
    have : (fun t => -rinf x t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      simp [rinf_neg (show u < 0 from hu)]
    exact (continuousAt_const.congr this.symm)
  · rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    have h2 := Metric.tendsto_nhds.1 (hx.1 t ht) (ε / 2) (half_pos hε)
    obtain ⟨u', hu't, hu'⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
    filter_upwards [Ico_mem_nhdsGE hu't] with u hu
    have hm1 : rinf x u ≤ rinf x t := by
      have := vstar_mono hx hx0 hu.1
      simpa using this
    have hm2 : rinf x t - ε / 2 ≤ rinf x u := by
      apply le_rinf (ht.trans hu.1)
      intro z hz
      rcases le_or_gt z t with hzt | hzt
      · have := rinf_le hx ⟨hz.1, hzt⟩
        linarith
      · have hzz : z ∈ Ico t u' := ⟨hzt.le, lt_of_le_of_lt hz.2 hu.2⟩
        have hb : |x z - x t| < ε / 2 := by
          have := hu' hzz
          simpa [Real.dist_eq] using this
        have := rinf_le hx ⟨ht, le_rfl⟩
        have := neg_abs_le (x z - x t)
        linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith


/-- The Stieltjes function `v*`. -/
noncomputable def vF {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) : StieltjesFunction ℝ where
  toFun := fun t => -rinf x t
  mono' := vstar_mono hx hx0
  right_continuous' := vstar_rc hx hx0

lemma vF_apply {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) (t : ℝ) :
    vF hx hx0 t = -rinf x t := rfl

lemma compl_aux {x : ℝ → ℝ} (hx : IsCadlag x) (hx0 : x 0 = 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : rinf x s < x s) : ∃ u, s < u ∧ (vF hx hx0).measure (Icc s u) = 0 := by
  set F := vF hx hx0
  have hd : 0 < x s - rinf x s := by linarith
  have h2 := Metric.tendsto_nhds.1 (hx.1 s hs0) (x s - rinf x s) hd
  obtain ⟨u', hu's, hu'⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
  have hu's' : s < u' := hu's
  refine ⟨(s + u') / 2, by linarith, ?_⟩
  rw [StieltjesFunction.measure_Icc, ENNReal.ofReal_eq_zero]
  have hu : F ((s + u') / 2) ≤ F s := by
    rw [vF_apply, vF_apply, neg_le_neg_iff]
    apply le_rinf (by linarith)
    intro z hz
    rcases le_or_gt z s with hzs | hzs
    · exact rinf_le hx ⟨hz.1, hzs⟩
    · have hzz : z ∈ Ico s u' := ⟨hzs.le, by linarith [hz.2]⟩
      have hb : |x z - x s| < x s - rinf x s := by
        have := hu' hzz
        simpa [Real.dist_eq] using this
      have := neg_abs_le (x z - x s)
      linarith
  have hl : F s ≤ Function.leftLim F s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hlt : rinf x s < rinf x s + min ε (x s - rinf x s) := by
      have := lt_min hε hd
      linarith
    haveI : Nonempty (Icc (0 : ℝ) s) := ⟨⟨0, le_rfl, hs0⟩⟩
    obtain ⟨⟨z, hz⟩, hzx⟩ := exists_lt_of_ciInf_lt (f := fun z : Icc (0 : ℝ) s => x z) hlt
    simp only at hzx
    have hzs : z < s := by
      rcases eq_or_lt_of_le hz.2 with h | h
      · subst h
        have := min_le_right ε (x z - rinf x z)
        linarith
      · exact h
    have h1 := F.mono.le_leftLim hzs
    have h3 : F z = -rinf x z := vF_apply hx hx0 z
    have h4 := rinf_le hx (z := z) (t := z) ⟨hz.1, le_rfl⟩
    have h5 := min_le_left ε (x s - rinf x s)
    rw [vF_apply]
    linarith
  linarith

end BWSkorokhodAux

open BWSkorokhodAux in
theorem solution (x : ℝ → ℝ) (hx : BellWilliams2001.ThresholdPolicy.IsCadlag x) (hx0 : x 0 = 0) :
    let vstar : ℝ → ℝ := fun t => -(⨅ s : Set.Icc (0 : ℝ) t, x s)
    let wstar : ℝ → ℝ := fun t => x t + vstar t
    let Cond : (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun w v =>
      BellWilliams2001.ThresholdPolicy.IsCadlag w ∧ BellWilliams2001.ThresholdPolicy.IsCadlag v ∧
      (∀ t : ℝ, 0 ≤ t → w t = x t + v t ∧ 0 ≤ w t) ∧
      MonotoneOn v (Set.Ici 0) ∧ v 0 = 0
    let Compl : (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun w v =>
      ∃ F : StieltjesFunction ℝ, (∀ t : ℝ, F t = v (max t 0)) ∧
        F.measure {s : ℝ | 0 ≤ s ∧ 0 < w s} = 0
    (∀ w v : ℝ → ℝ, Cond w v → Compl w v → ∀ t : ℝ, 0 ≤ t → w t = wstar t ∧ v t = vstar t) ∧
    Cond wstar vstar ∧ Compl wstar vstar ∧
    (∀ w v : ℝ → ℝ, Cond w v → ∀ t : ℝ, 0 ≤ t → vstar t ≤ v t ∧ wstar t ≤ w t) := by
  intro vstar wstar Cond Compl
  have hvs : ∀ t, vstar t = -rinf x t := fun t => rfl
  have hws : ∀ t, wstar t = x t + -rinf x t := fun t => rfl
  have hmin : ∀ w v : ℝ → ℝ, Cond w v → ∀ t : ℝ, 0 ≤ t → vstar t ≤ v t ∧ wstar t ≤ w t := by
    rintro w v ⟨-, -, hwx, hmono, -⟩ t ht
    have h1 : vstar t ≤ v t := by
      rw [hvs]
      have : -v t ≤ rinf x t := le_rinf ht fun z hz => by
        have h1 := hwx z hz.1
        have h2 := hmono hz.1 ht hz.2
        linarith
      linarith
    refine ⟨h1, ?_⟩
    rw [hws, (hwx t ht).1]
    rw [hvs] at h1
    linarith
  refine ⟨?_, ?_, ?_, hmin⟩
  · intro w v hC hCo t ht
    have hm := hmin w v hC t ht
    obtain ⟨-, -, hwx, hmono, hv0⟩ := hC
    obtain ⟨F, hF, hnull⟩ := hCo
    suffices hle : v t ≤ vstar t by
      have hveq : v t = vstar t := le_antisymm hle hm.1
      refine ⟨?_, hveq⟩
      rw [(hwx t ht).1, hveq]
    by_contra hlt
    push_neg at hlt
    set a := vstar t with ha
    have ha0 : 0 ≤ a := by
      have := vstar_mono hx hx0 ht
      simp only [rinf_zero hx hx0, neg_zero] at this
      rw [ha, hvs]; exact this
    have hax : ∀ s ∈ Icc (0 : ℝ) t, -x s ≤ a := by
      intro s hs
      rw [ha, hvs]
      have := rinf_le hx hs
      linarith
    set S := {s | s ∈ Icc (0 : ℝ) t ∧ v s ≤ a} with hS
    set σ := sSup S with hσ
    have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht⟩, by rw [hv0]; exact ha0⟩
    have hSbdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
    have hσ0 : 0 ≤ σ := le_csSup hSbdd ⟨⟨le_rfl, ht⟩, by rw [hv0]; exact ha0⟩
    have hσt : σ ≤ t := csSup_le hSne (fun s hs => hs.1.2)
    have fact1 : ∀ s, σ < s → s ≤ t → 0 < w s := by
      intro s h1 h2
      have hvs' : a < v s := by
        by_contra hc
        push_neg at hc
        have := le_csSup hSbdd ⟨⟨hσ0.trans h1.le, h2⟩, hc⟩
        linarith
      rw [(hwx s (hσ0.trans h1.le)).1]
      linarith [hax s ⟨hσ0.trans h1.le, h2⟩]
    have fact2 : ∀ s, s < σ → F s ≤ a := by
      intro s hs
      rw [hF s]
      rcases lt_or_ge s 0 with h | h
      · rw [max_eq_right h.le, hv0]; exact ha0
      · rw [max_eq_left h]
        obtain ⟨s', hs'S, hss'⟩ := exists_lt_of_lt_csSup hSne hs
        exact (hmono (show s ∈ Ici (0 : ℝ) from h) (show s' ∈ Ici (0 : ℝ) from hs'S.1.1)
          hss'.le).trans hs'S.2
    have hFt : F t = v t := by rw [hF, max_eq_left ht]
    by_cases hwσ : 0 < w σ
    · have hsub : Icc σ t ⊆ {s | 0 ≤ s ∧ 0 < w s} := by
        intro s hs
        refine ⟨hσ0.trans hs.1, ?_⟩
        rcases eq_or_lt_of_le hs.1 with h | h
        · rw [← h]; exact hwσ
        · exact fact1 s h hs.2
      have h0 := measure_mono_null hsub hnull
      rw [StieltjesFunction.measure_Icc, ENNReal.ofReal_eq_zero] at h0
      have hll : Function.leftLim F σ ≤ a := by
        apply le_of_tendsto (F.mono.tendsto_leftLim σ)
        exact eventually_nhdsWithin_of_forall fun s hs => fact2 s hs
      linarith
    · have hvσ : v σ ≤ a := by
        have h1 := (hwx σ hσ0).1
        have h3 := hax σ ⟨hσ0, hσt⟩
        push_neg at hwσ
        linarith
      have hsub : Ioc σ t ⊆ {s | 0 ≤ s ∧ 0 < w s} := fun s hs =>
        ⟨hσ0.trans hs.1.le, fact1 s hs.1 hs.2⟩
      have h0 := measure_mono_null hsub hnull
      rw [StieltjesFunction.measure_Ioc, ENNReal.ofReal_eq_zero] at h0
      have hFσ : F σ = v σ := by rw [hF, max_eq_left hσ0]
      linarith
  · refine ⟨⟨fun t ht => (hx.1 t ht).add (vstar_rc hx hx0 t), fun t ht => ?_⟩,
      ⟨fun t _ => vstar_rc hx hx0 t, fun t _ => ⟨_, (vstar_mono hx hx0).tendsto_leftLim t⟩⟩,
      fun t ht => ⟨rfl, ?_⟩, (vstar_mono hx hx0).monotoneOn _, ?_⟩
    · obtain ⟨l, hl⟩ := hx.2 t ht
      exact ⟨_, hl.add ((vstar_mono hx hx0).tendsto_leftLim t)⟩
    · rw [hws]
      linarith [rinf_le hx (z := t) (t := t) ⟨ht, le_rfl⟩]
    · rw [hvs, rinf_zero hx hx0, neg_zero]
  · refine ⟨vF hx hx0, fun t => ?_, ?_⟩
    · rw [vF_apply, ← hvs]
      rcases le_or_gt 0 t with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h.le, hvs, hvs, rinf_neg h, rinf_zero hx hx0]
    · apply null_of_right_null
      rintro s ⟨hs0, hs⟩
      rw [hws] at hs
      exact compl_aux hx hx0 hs0 (by linarith)
