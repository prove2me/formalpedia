-- Prove2me | solution 1 for EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:37:50.528195+00:00
-- url     : https://prove2.me/submissions/aea7b72e-c6c4-41e4-8757-d4e639c1f348

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

namespace CSSAux

/-- The sweep: on `[0,1/2]` sweep the tail at double speed; on `[1/2,1]` grow the head interval
`[x, b)` from `x = b` down to `x = a`. -/
noncomputable def sweep : Piece → ℝ → Set ℝ
  | [] => fun _ => ∅
  | I :: rest => fun t =>
      if t ≤ 1 / 2 then sweep rest (2 * t)
      else Interval.toSet ⟨I.b - (2 * t - 1) * (I.b - I.a), I.b⟩ ∪ (Piece.toSet rest)

theorem toSet_cons (I : Interval) (rest : Piece) :
    Piece.toSet (I :: rest) = I.toSet ∪ (Piece.toSet rest) := by
  ext x; simp [Piece.toSet]

theorem interval_measurable (I : Interval) : MeasurableSet I.toSet := by
  unfold Interval.toSet; split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem piece_measurable (P : Piece) : MeasurableSet P.toSet := by
  have : P.toSet = ⋃ I ∈ P, I.toSet := by ext x; simp [Piece.toSet]
  rw [this]
  exact MeasurableSet.biUnion P.finite_toSet.countable (fun I _ => interval_measurable I)

theorem ivl_empty (b : ℝ) : Interval.toSet ⟨b, b⟩ = ∅ := by
  simp [Interval.toSet]

theorem ivl_mono {x x' b : ℝ} (h : x' ≤ x) :
    Interval.toSet ⟨x, b⟩ ⊆ Interval.toSet ⟨x', b⟩ := by
  intro y hy
  simp only [Interval.toSet] at hy ⊢
  split_ifs at hy with h1 <;> split_ifs with h2
  · exact ⟨le_trans h hy.1, hy.2⟩
  · exact absurd ⟨h1.1, lt_of_le_of_lt h h1.2⟩ h2
  · exact ⟨le_trans h hy.1, hy.2.le⟩
  · exact ⟨le_trans h hy.1, hy.2⟩

theorem value_mono (v : Valuation) {A B : Set ℝ} (h : A ⊆ B) (hB : MeasurableSet B) :
    v.value A ≤ v.value B := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_forall_mem (hB.inter measurableSet_Icc)
      (fun x hx => v.nonneg x hx.2)
  · exact (Set.inter_subset_inter_left _ h).eventuallyLE

theorem value_union (v : Valuation) {A B : Set ℝ} (hB : MeasurableSet B) (hd : Disjoint A B) :
    v.value (A ∪ B) = v.value A + v.value B := by
  unfold Valuation.value
  rw [Set.union_inter_distrib_right]
  apply MeasureTheory.setIntegral_union
  · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hd
  · exact hB.inter measurableSet_Icc
  · exact v.integrable.mono_set Set.inter_subset_right
  · exact v.integrable.mono_set Set.inter_subset_right

theorem value_empty (v : Valuation) : v.value ∅ = 0 := by simp [Valuation.value]

/-- The value of `[x, b)` (or `[x, b]`) as an interval integral of the truncated density. -/
theorem value_ivl (v : Valuation) {x b : ℝ} (hxb : x ≤ b) :
    v.value (Interval.toSet ⟨x, b⟩) =
      ∫ y in x..b, (Set.Icc (0 : ℝ) 1).indicator v.density y := by
  rw [intervalIntegral.integral_of_le hxb]
  unfold Valuation.value
  rw [← MeasureTheory.setIntegral_indicator measurableSet_Icc]
  simp only [Interval.toSet]
  split_ifs
  · exact MeasureTheory.integral_Icc_eq_integral_Ioc
  · exact MeasureTheory.integral_Ico_eq_integral_Ioc

theorem suffix_cons (I : Interval) (rest : Piece) (X : Set ℝ) (h : IsSuffix X rest) :
    IsSuffix X (I :: rest) := by
  rcases h with h | ⟨⟨k, x⟩, hp, rfl⟩
  · exact Or.inl h
  · refine Or.inr ⟨(k + 1, x), ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨by simp; omega, by simpa using h2, by simpa using h3⟩
    · obtain ⟨h1, -, -⟩ := hp
      simp only [suffixList, List.length_cons]
      rw [if_pos h1, if_pos (by omega)]
      simp

theorem sweep_spec : ∀ (Q : Piece), Q.WF →
    sweep Q 0 = ∅ ∧ sweep Q 1 = Q.toSet ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, IsSuffix (sweep Q t) Q) ∧
    MonotoneOn (sweep Q) (Set.Icc (0 : ℝ) 1) ∧
    ∀ v : Valuation, ContinuousOn (fun t ↦ v.value (sweep Q t)) (Set.Icc (0 : ℝ) 1) := by
  intro Q
  induction Q with
  | nil =>
    intro _
    refine ⟨rfl, by simp [sweep, Piece.toSet], fun t _ => Or.inl rfl, ?_, fun v => ?_⟩
    · intro s _ t _ _; exact le_rfl
    · simp only [sweep]; exact continuousOn_const
  | cons I rest ih =>
    intro hQ
    have hrest : Piece.WF rest := ⟨fun J hJ => hQ.1 J (List.mem_cons_of_mem _ hJ),
      (List.pairwise_cons.mp hQ.2).2⟩
    have hI := hQ.1 I (List.mem_cons_self ..)
    have hdisj : Disjoint I.toSet (Piece.toSet rest) := by
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨J, hJ, hyJ⟩ := hy'
      exact Set.disjoint_left.mp ((List.pairwise_cons.mp hQ.2).1 J hJ) hy hyJ
    obtain ⟨h0, h1, hsuf, hmono, hcont⟩ := ih hrest
    set a := I.a
    set b := I.b
    have hab : a ≤ b := hI.2.1
    let x : ℝ → ℝ := fun t => b - (2 * t - 1) * (b - a)
    have hxab : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, a ≤ x t ∧ x t ≤ b := by
      intro t ht; simp only [x]; constructor <;> nlinarith [ht.1, ht.2]
    have hsub_I : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, Interval.toSet ⟨x t, b⟩ ⊆ I.toSet := by
      intro t ht
      have := ivl_mono (b := b) (hxab t ht).1
      simpa using this
    have hhi : ∀ t, 1 / 2 < t → sweep (I :: rest) t = Interval.toSet ⟨x t, b⟩ ∪ (Piece.toSet rest) := by
      intro t ht; simp only [sweep, if_neg (not_le.mpr ht)]; rfl
    have hlo : ∀ t, t ≤ 1 / 2 → sweep (I :: rest) t = sweep rest (2 * t) := by
      intro t ht; simp only [sweep, if_pos ht]
    have hrest_sub : ∀ s ∈ Set.Icc (0 : ℝ) 1, sweep rest s ⊆ (Piece.toSet rest) := by
      intro s hs; rw [← h1]; exact hmono hs ⟨by norm_num, le_rfl⟩ hs.2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hlo 0 (by norm_num)]; simpa using h0
    · have hx1 : x 1 = a := by simp only [x]; ring
      rw [hhi 1 (by norm_num), toSet_cons, hx1]
    · intro t ht
      by_cases htl : t ≤ 1 / 2
      · rw [hlo t htl]
        exact suffix_cons I rest _ (hsuf _ ⟨by linarith [ht.1], by linarith⟩)
      · have ht' : t ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith, ht.2⟩
        rw [hhi t (not_le.mp htl)]
        refine Or.inr ⟨(0, x t), ⟨by simp, by simpa using (hxab t ht').1,
          by simpa using (hxab t ht').2⟩, ?_⟩
        simp [suffixList, toSet_cons, b]
    · intro s hs t ht hst
      by_cases hsl : s ≤ 1 / 2
      · rw [hlo s hsl]
        by_cases htl : t ≤ 1 / 2
        · rw [hlo t htl]
          exact hmono ⟨by linarith [hs.1], by linarith⟩ ⟨by linarith [ht.1], by linarith⟩
            (by linarith)
        · rw [hhi t (not_le.mp htl)]
          exact (hrest_sub _ ⟨by linarith [hs.1], by linarith⟩).trans Set.subset_union_right
      · have htl : ¬ t ≤ 1 / 2 := by intro h; exact hsl (le_trans hst h)
        rw [hhi s (not_le.mp hsl), hhi t (not_le.mp htl)]
        apply Set.union_subset_union_left
        apply ivl_mono
        simp only [x]; nlinarith
    · intro v
      have hA : ContinuousOn (fun t ↦ v.value (sweep (I :: rest) t)) (Set.Icc 0 (1 / 2)) := by
        have hc := (hcont v).comp (continuous_const.mul continuous_id).continuousOn
          (fun t (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) => (⟨by linarith [ht.1], by linarith [ht.2]⟩ :
            2 * t ∈ Set.Icc (0 : ℝ) 1))
        refine hc.congr (fun t ht => ?_)
        change v.value (sweep (I :: rest) t) = v.value (sweep rest (2 * t))
        rw [hlo t ht.2]
      have hB : ContinuousOn (fun t ↦ v.value (sweep (I :: rest) t)) (Set.Icc (1 / 2) 1) := by
        let F := (Set.Icc (0 : ℝ) 1).indicator v.density
        have hF : MeasureTheory.Integrable F := by
          rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]; exact v.integrable
        have hψ : ContinuousOn (fun y => ∫ z in y..b, F z) (Set.uIcc a b) :=
          intervalIntegral.continuousOn_primitive_interval_left hF.integrableOn
        have hxc : ContinuousOn x (Set.Icc (1 / 2 : ℝ) 1) := by
          apply Continuous.continuousOn; simp only [x]; fun_prop
        have hcomp := (hψ.comp hxc (fun t ht => by
          rw [Set.uIcc_of_le hab]; exact hxab t ht)).add
            (continuousOn_const (c := v.value (Piece.toSet rest)))
        refine hcomp.congr (fun t ht => ?_)
        change v.value (sweep (I :: rest) t) = (∫ z in x t..b, F z) + v.value (Piece.toSet rest)
        rcases eq_or_lt_of_le ht.1 with heq | hlt
        · subst heq
          have hx : x (1 / 2) = b := by simp only [x]; ring
          rw [hlo _ le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, h1, hx,
            intervalIntegral.integral_same, zero_add]
        · rw [hhi t hlt, value_union v (piece_measurable rest)
            (Disjoint.mono_left (hsub_I t ht) hdisj), value_ivl v (hxab t ht).2]
      have := hA.union_of_isClosed hB isClosed_Icc isClosed_Icc
      rwa [Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

end CSSAux

open CSSAux in
theorem solution
    (Q : Piece) (hQ : Q.WF) :
    ∃ S : ℝ → Set ℝ,
      S 0 = ∅ ∧ S 1 = Q.toSet ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsSuffix (S t) Q) ∧
      MonotoneOn S (Set.Icc (0 : ℝ) 1) ∧
      ∀ v : Valuation,
        ContinuousOn (fun t ↦ v.value (S t)) (Set.Icc (0 : ℝ) 1) ∧
        MonotoneOn (fun t ↦ v.value (S t)) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨h0, h1, hsuf, hmono, hcont⟩ := sweep_spec Q hQ
  refine ⟨sweep Q, h0, h1, hsuf, hmono, fun v => ⟨hcont v, ?_⟩⟩
  intro s hs t ht hst
  apply value_mono v (hmono hs ht hst)
  rcases hsuf t ht with h | ⟨p, -, h⟩
  · rw [h]; exact MeasurableSet.empty
  · rw [h]; exact piece_measurable _
