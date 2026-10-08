-- Prove2me | solution 1 for AvgCompletionSched.BestAlpha.alpha_schedule_completion_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T13:02:30.195626+00:00
-- url     : https://prove2.me/submissions/61acb36c-5120-4f8b-b0e7-e9df3ea49e8f

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model



namespace AvgCompletionSched.BestAlpha

open MeasureTheory

variable {n : ℕ} {I : Instance n}

lemma ba_run_ne_top (P : PreemptiveSchedule I) (j : Fin n) (A : Set ℝ) :
    volume ({s | P.σ s = some j} ∩ A) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [P.total j]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

lemma ba_done_mono (P : PreemptiveSchedule I) (j : Fin n) {t t' : ℝ} (h : t ≤ t') :
    P.done j t ≤ P.done j t' := by
  unfold PreemptiveSchedule.done
  exact ENNReal.toReal_mono (ba_run_ne_top P j _)
    (measure_mono (Set.inter_subset_inter_right _ (Set.Ico_subset_Ico_right h)))

lemma ba_done_le (P : PreemptiveSchedule I) (j : Fin n) (t : ℝ) : P.done j t ≤ I.p j := by
  unfold PreemptiveSchedule.done
  have := ENNReal.toReal_mono (by rw [P.total j]; exact ENNReal.ofReal_ne_top)
    (measure_mono (μ := volume)
      (Set.inter_subset_left : {s | P.σ s = some j} ∩ Set.Ico 0 t ⊆ _))
  rw [P.total j, ENNReal.toReal_ofReal (I.p_pos j).le] at this
  exact this

lemma ba_done_lip (P : PreemptiveSchedule I) (j : Fin n) {t t' : ℝ} (h : t ≤ t') :
    P.done j t' ≤ P.done j t + (t' - t) := by
  unfold PreemptiveSchedule.done
  have hsub : {s | P.σ s = some j} ∩ Set.Ico 0 t' ⊆
      ({s | P.σ s = some j} ∩ Set.Ico 0 t) ∪ Set.Ico t t' := by
    intro s ⟨hs1, hs2⟩
    by_cases hst : s < t
    · exact Or.inl ⟨hs1, hs2.1, hst⟩
    · exact Or.inr ⟨le_of_not_gt hst, hs2.2⟩
  have h1 := measure_mono (μ := volume) hsub
  have h2 := measure_union_le (μ := volume) ({s | P.σ s = some j} ∩ Set.Ico 0 t) (Set.Ico t t')
  rw [Real.volume_Ico] at h2
  have h3 := h1.trans h2
  have := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ba_run_ne_top P j _, ENNReal.ofReal_ne_top⟩) h3
  rwa [ENNReal.toReal_add (ba_run_ne_top P j _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at this

lemma ba_done_zero (P : PreemptiveSchedule I) (j : Fin n) {t : ℝ} (h : t ≤ I.r j) :
    P.done j t = 0 := by
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Set.Ico 0 t = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hs, -, hst⟩
    have := P.released s j hs
    linarith
  rw [this]; simp

lemma ba_done_eventually (P : PreemptiveSchedule I) (j : Fin n) :
    ∃ T, ∀ t, T ≤ t → P.done j t = I.p j := by
  obtain ⟨T, hT⟩ := P.bounded j
  refine ⟨T, fun t ht => ?_⟩
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Set.Ico 0 t = {s | P.σ s = some j} := by
    apply Set.inter_eq_left.2
    intro s hs
    exact ⟨P.nonneg s j hs, (hT s hs).trans_le ht⟩
  rw [this, P.total j, ENNReal.toReal_ofReal (I.p_pos j).le]

lemma ba_set_nonempty (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα1 : α ≤ 1) :
    {t | α * I.p j ≤ P.done j t}.Nonempty := by
  obtain ⟨T, hT⟩ := ba_done_eventually P j
  refine ⟨T, ?_⟩
  show α * I.p j ≤ P.done j T
  rw [hT T le_rfl]
  have := I.p_pos j
  nlinarith

lemma ba_r_le_of_mem (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) {t : ℝ}
    (ht : α * I.p j ≤ P.done j t) : I.r j ≤ t := by
  by_contra h
  push_neg at h
  have h1 := ba_done_zero P j h.le
  have := I.p_pos j
  nlinarith [mul_pos hα0 this]

lemma ba_set_bdd (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) :
    BddBelow {t | α * I.p j ≤ P.done j t} :=
  ⟨I.r j, fun _ ht => ba_r_le_of_mem P j hα0 ht⟩

lemma ba_r_le_CPα (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    I.r j ≤ P.CPα j α :=
  le_csInf (ba_set_nonempty P j hα1) (fun _ ht => ba_r_le_of_mem P j hα0 ht)

lemma ba_CPα_le (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) {t : ℝ}
    (h : α * I.p j ≤ P.done j t) : P.CPα j α ≤ t :=
  csInf_le (ba_set_bdd P j hα0) h

lemma ba_done_CPα (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    P.done j (P.CPα j α) = α * I.p j := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    have hnot : ¬ (α * I.p j ≤ P.done j (P.CPα j α - ε / 2)) := by
      intro h
      have := ba_CPα_le P j hα0 h
      linarith
    push_neg at hnot
    have := ba_done_lip P j (show P.CPα j α - ε / 2 ≤ P.CPα j α by linarith)
    linarith
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨s, hs, hs2⟩ := exists_lt_of_csInf_lt (ba_set_nonempty P j hα1)
      (show sInf {t | α * I.p j ≤ P.done j t} < P.CPα j α + ε / 2 by
        show P.CPα j α < P.CPα j α + ε / 2; linarith)
    have h1 := ba_done_mono P j hs2.le
    have h2 := ba_done_lip P j (show P.CPα j α ≤ P.CPα j α + ε / 2 by linarith)
    have h3 : α * I.p j ≤ P.done j s := hs
    linarith

lemma ba_CP_eq (P : PreemptiveSchedule I) (j : Fin n) : P.CP j = P.CPα j 1 := by
  unfold PreemptiveSchedule.CP PreemptiveSchedule.CPα
  simp only [one_mul]

lemma ba_done_CP (P : PreemptiveSchedule I) (j : Fin n) : P.done j (P.CP j) = I.p j := by
  rw [ba_CP_eq, ba_done_CPα P j one_pos le_rfl, one_mul]

lemma ba_CPα_le_CP (P : PreemptiveSchedule I) (j : Fin n) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    P.CPα j α ≤ P.CP j := by
  apply ba_CPα_le P j hα0
  rw [ba_done_CP]
  have := I.p_pos j
  nlinarith

lemma ba_meas (P : PreemptiveSchedule I) (o : Option (Fin n)) :
    MeasurableSet {s | P.σ s = o} := by
  cases o with
  | some j => exact P.measurableSet_run j
  | none =>
    have : {s | P.σ s = none} = (⋃ j, {s | P.σ s = some j})ᶜ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h j h'; rw [h] at h'; exact absurd h' (by simp)
      · intro h
        cases hs : P.σ s with
        | none => rfl
        | some j => exact absurd hs (h j)
    rw [this]
    exact (MeasurableSet.iUnion fun j => P.measurableSet_run j).compl

lemma ba_decomp (P : PreemptiveSchedule I) {t : ℝ} (ht : 0 ≤ t) :
    (volume ({s | P.σ s = none} ∩ Set.Ico 0 t)).toReal + ∑ j, P.done j t = t := by
  have hU : Set.Ico (0:ℝ) t = ⋃ o ∈ (Finset.univ : Finset (Option (Fin n))),
      ({s | P.σ s = o} ∩ Set.Ico 0 t) := by
    ext s; simp
  have hvol : volume (Set.Ico (0:ℝ) t) =
      ∑ o : Option (Fin n), volume ({s | P.σ s = o} ∩ Set.Ico 0 t) := by
    conv_lhs => rw [hU]
    apply measure_biUnion_finset
    · intro a _ b _ hab
      apply Set.disjoint_left.2
      intro s h1 h2
      exact hab (h1.1.symm.trans h2.1)
    · intro o _
      exact (ba_meas P o).inter measurableSet_Ico
  have hfin : ∀ o : Option (Fin n), volume ({s | P.σ s = o} ∩ Set.Ico 0 t) ≠ ⊤ := by
    intro o
    exact ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have := congrArg ENNReal.toReal hvol
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_sum (fun o _ => hfin o),
    Fintype.sum_option, sub_zero] at this
  exact this.symm

lemma ba_listFinish (π : Fin n ≃ Fin n) : ∀ k, 0 < k → k ≤ n →
    ∃ l, l < k ∧ ∃ hl : l < n, listFinish I π k ≤ I.r (π ⟨l, hl⟩) +
      ∑ j, (if l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k then I.p j else 0)
  | 0, h, _ => absurd h (lt_irrefl 0)
  | k+1, _, hk => by
    have hkn : k < n := hk
    have hrec : listFinish I π (k+1) =
        max (I.r (π ⟨k, hkn⟩)) (listFinish I π k) + I.p (π ⟨k, hkn⟩) := by
      rw [listFinish, dif_pos hkn]
    have hsum : ∀ l, l ≤ k → ∑ j, (if l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k+1 then I.p j else 0)
        = ∑ j, (if l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k then I.p j else 0)
          + I.p (π ⟨k, hkn⟩) := by
      intro l hl
      have e : I.p (π ⟨k, hkn⟩) = ∑ j, (if π ⟨k, hkn⟩ = j then I.p j else 0) := by simp
      rw [e, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have key : (π.symm j : ℕ) = k ↔ j = π ⟨k, hkn⟩ := by
        constructor
        · intro h
          rw [← Equiv.apply_symm_apply π j]
          congr 1
          exact Fin.ext h
        · rintro rfl; simp
      by_cases h1 : (π.symm j : ℕ) = k
      · have h2 := key.1 h1
        rw [if_pos h2.symm, if_pos ⟨h1 ▸ hl, by omega⟩, if_neg (by omega)]
        rw [h2]; ring
      · have h2 : ¬ (π ⟨k, hkn⟩ = j) := fun h => h1 (key.2 h.symm)
        rw [if_neg h2, add_zero]
        by_cases h3 : l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k
        · rw [if_pos h3, if_pos ⟨h3.1, by omega⟩]
        · rw [if_neg h3, if_neg (by omega)]
    by_cases hc : listFinish I π k ≤ I.r (π ⟨k, hkn⟩)
    · refine ⟨k, by omega, hkn, ?_⟩
      rw [hrec, max_eq_left hc, hsum k le_rfl]
      have : ∑ j, (if k ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k then I.p j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (by omega)]
      rw [this]; linarith
    · push_neg at hc
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          have : listFinish I π 0 = 0 := rfl
          have := I.r_nonneg (π ⟨0, hkn⟩)
          linarith
        · exact h
      obtain ⟨l, hlk, hl, hb⟩ := ba_listFinish π k hk0 (by omega)
      refine ⟨l, by omega, hl, ?_⟩
      rw [hrec, max_eq_right hc.le, hsum l hlk.le]
      linarith

theorem alpha_bound_core (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤
      P.idle i + ∑ j, ((if α ≤ P.frac i j then (1 + α) * I.p j else 0) +
        (if P.frac i j < α then P.frac i j * I.p j else 0)) := by
  obtain ⟨hα0, hα1⟩ := hα
  have hord : ∀ j j' : Fin n, π.symm j ≤ π.symm j' → P.CPα j α ≤ P.CPα j' α := by
    intro j j' h
    have := hπ _ _ h
    simpa using this
  set k0 : ℕ := (π.symm i : ℕ) with hk0
  obtain ⟨l, hlk, hl, hb⟩ := ba_listFinish (I := I) π (k0 + 1) (by omega) (by
    have := (π.symm i).isLt; omega)
  set a := π ⟨l, hl⟩ with ha
  have hsa : π.symm a = ⟨l, hl⟩ := by simp [ha]
  have hρa : I.r a ≤ P.CPα a α := ba_r_le_CPα P a hα0 hα1
  have hai : P.CPα a α ≤ P.CPα i α := hord a i (by
    rw [hsa]; show l ≤ (π.symm i : ℕ); omega)
  have hiCP : P.CPα i α ≤ P.CP i := ba_CPα_le_CP P i hα0 hα1
  have hρ0 : 0 ≤ I.r a := I.r_nonneg a
  have hdec := ba_decomp P hρ0
  have hidle : (volume ({s | P.σ s = none} ∩ Set.Ico 0 (I.r a))).toReal ≤ P.idle i := by
    unfold PreemptiveSchedule.idle
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_right)
    · exact measure_mono (Set.inter_subset_inter_right _
        (Set.Ico_subset_Ico_right (by linarith)))
  have hlc : listCompletion I π i = listFinish I π (k0 + 1) := rfl
  rw [hlc]
  refine hb.trans ?_
  rw [← hdec, add_assoc, ← Finset.sum_add_distrib]
  apply add_le_add hidle
  apply Finset.sum_le_sum
  intro j _
  have hp := I.p_pos j
  have hfr : P.frac i j * I.p j = P.done j (P.CP i) := by
    unfold PreemptiveSchedule.frac; field_simp
  have hfrac : α ≤ P.frac i j ↔ α * I.p j ≤ P.done j (P.CP i) := by
    unfold PreemptiveSchedule.frac; rw [le_div_iff₀ hp]
  have hJ : (π.symm j : ℕ) ≤ k0 → α ≤ P.frac i j := by
    intro h
    rw [hfrac]
    have h1 : P.CPα j α ≤ P.CPα i α := hord j i (by show (π.symm j : ℕ) ≤ (π.symm i : ℕ); omega)
    have := ba_done_mono P j (h1.trans hiCP)
    rw [ba_done_CPα P j hα0 hα1] at this
    exact this
  have hdle := ba_done_le P j (I.r a)
  by_cases hx : α ≤ P.frac i j
  · rw [if_pos hx, if_neg (not_lt.2 hx), add_zero]
    by_cases hj : l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k0 + 1
    · rw [if_pos hj]
      have h1 : P.CPα a α ≤ P.CPα j α := hord a j (by rw [hsa]; show l ≤ (π.symm j : ℕ); exact hj.1)
      have := ba_done_mono P j (hρa.trans h1)
      rw [ba_done_CPα P j hα0 hα1] at this
      nlinarith
    · rw [if_neg hj]; nlinarith
  · rw [if_neg hx, if_pos (lt_of_not_ge hx), zero_add, hfr]
    have hj : ¬ (l ≤ (π.symm j : ℕ) ∧ (π.symm j : ℕ) < k0 + 1) := by
      rintro ⟨_, h2⟩; exact hx (hJ (by omega))
    rw [if_neg hj, add_zero]
    exact ba_done_mono P j (by linarith)

theorem alpha_schedule_completion_bound_core {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤
      P.idle i + (1 + α) * ∑ j ∈ Finset.univ.filter (fun j => α ≤ P.frac i j), I.p j
        + ∑ j ∈ Finset.univ.filter (fun j => P.frac i j < α), P.frac i j * I.p j := by
  have := alpha_bound_core P α hα π hπ i
  rw [Finset.sum_add_distrib] at this
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  simp only [mul_ite, mul_zero] at this ⊢
  linarith

end AvgCompletionSched.BestAlpha

open AvgCompletionSched.BestAlpha


theorem solution {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤
      P.idle i + (1 + α) * ∑ j ∈ Finset.univ.filter (fun j => α ≤ P.frac i j), I.p j
        + ∑ j ∈ Finset.univ.filter (fun j => P.frac i j < α), P.frac i j * I.p j := by
  exact alpha_schedule_completion_bound_core P α hα π hπ i
