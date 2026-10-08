-- Prove2me | solution 1 for AvgCompletionSched.BestAlpha.best_alpha_approximation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T13:08:35.694271+00:00
-- url     : https://prove2.me/submissions/6aedfbb8-b82c-413c-9167-69c8c1a2b0ca

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

noncomputable def baσN (N : NonpreemptiveSchedule I) (t : ℝ) : Option (Fin n) :=
  if h : ∃ j, t ∈ Set.Ico (N.S j) (N.S j + I.p j) then some (Classical.choose h) else none

lemma baσN_iff (N : NonpreemptiveSchedule I) (t : ℝ) (j : Fin n) :
    baσN N t = some j ↔ t ∈ Set.Ico (N.S j) (N.S j + I.p j) := by
  unfold baσN
  split_ifs with h
  · have hs := Classical.choose_spec h
    constructor
    · intro e; simp only [Option.some.injEq] at e; rw [← e]; exact hs
    · intro ht
      simp only [Option.some.injEq]
      by_contra hne
      rcases N.noOverlap _ _ hne with h1 | h1
      · linarith [hs.2, ht.1]
      · linarith [ht.2, hs.1]
  · constructor
    · intro e; exact absurd e (by simp)
    · intro ht; exact absurd ⟨j, ht⟩ h

lemma baσN_set (N : NonpreemptiveSchedule I) (j : Fin n) :
    {s | baσN N s = some j} = Set.Ico (N.S j) (N.S j + I.p j) := by
  ext s; exact baσN_iff N s j

noncomputable def baOfN (N : NonpreemptiveSchedule I) : PreemptiveSchedule I where
  σ := baσN N
  measurableSet_run j := by rw [baσN_set]; exact measurableSet_Ico
  nonneg t j h := by
    rw [baσN_iff] at h; linarith [h.1, N.released j, I.r_nonneg j]
  released t j h := by rw [baσN_iff] at h; linarith [h.1, N.released j]
  total j := by rw [baσN_set, Real.volume_Ico, add_sub_cancel_left]
  bounded j := ⟨N.S j + I.p j, fun s h => by rw [baσN_iff] at h; exact h.2⟩

lemma baOfN_CP (N : NonpreemptiveSchedule I) (j : Fin n) : (baOfN N).CP j ≤ N.C j := by
  rw [ba_CP_eq]
  apply ba_CPα_le _ j one_pos
  rw [one_mul]
  unfold PreemptiveSchedule.done
  have : {s | (baOfN N).σ s = some j} ∩ Set.Ico 0 (N.C j) =
      Set.Ico (N.S j) (N.S j + I.p j) := by
    rw [show (baOfN N).σ = baσN N from rfl, baσN_set]
    apply Set.inter_eq_left.2
    exact Set.Ico_subset_Ico (by linarith [N.released j, I.r_nonneg j]) le_rfl
  rw [this, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [I.p_pos j])]
  linarith

lemma ba_sum_CP_le (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (N : NonpreemptiveSchedule I) : ∑ j, w j * P.CP j ≤ ∑ j, w j * N.C j :=
  (hP (baOfN N)).trans (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (baOfN_CP N j) (hw j).le)

lemma ba_frac_mul (P : PreemptiveSchedule I) (i j : Fin n) :
    P.frac i j * I.p j = P.done j (P.CP i) := by
  unfold PreemptiveSchedule.frac; field_simp [(I.p_pos j).ne']

lemma ba_frac_nonneg (P : PreemptiveSchedule I) (i j : Fin n) : 0 ≤ P.frac i j :=
  div_nonneg ENNReal.toReal_nonneg (I.p_pos j).le

lemma ba_frac_le_one (P : PreemptiveSchedule I) (i j : Fin n) : P.frac i j ≤ 1 :=
  (div_le_one (I.p_pos j)).2 (ba_done_le P j _)

lemma ba_CP_nonneg (P : PreemptiveSchedule I) (i : Fin n) : 0 ≤ P.CP i :=
  (I.r_nonneg i).trans (by rw [ba_CP_eq]; exact ba_r_le_CPα P i one_pos le_rfl)

lemma ba_CP_decomp (P : PreemptiveSchedule I) (i : Fin n) :
    P.CP i = P.idle i + ∑ j, P.frac i j * I.p j := by
  have := ba_decomp P (ba_CP_nonneg P i)
  simp only [ba_frac_mul]
  unfold PreemptiveSchedule.idle
  linarith

lemma ba_idle_nonneg (P : PreemptiveSchedule I) (i : Fin n) : 0 ≤ P.idle i :=
  ENNReal.toReal_nonneg

noncomputable def baG (α x p : ℝ) : ℝ :=
  (if α ≤ x then (1 + α) * p else 0) + (if x < α then x * p else 0)

theorem ba_bound_G (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤ P.idle i + ∑ j, baG α (P.frac i j) (I.p j) :=
  alpha_bound_core P α hα π hπ i

lemma baG_two (x p : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hp : 0 < p) :
    3/5 * baG 1 x p + 2/5 * baG (1/2) x p ≤ 9/5 * (x * p) := by
  unfold baG; split_ifs <;> nlinarith

theorem two_point_core {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (π₁ π₂ : Fin n ≃ Fin n) (hπ₁ : IsAlphaOrder P 1 π₁) (hπ₂ : IsAlphaOrder P (1 / 2) π₂)
    (N : NonpreemptiveSchedule I) :
    3 / 5 * ∑ j, w j * listCompletion I π₁ j + 2 / 5 * ∑ j, w j * listCompletion I π₂ j
      ≤ 9 / 5 * ∑ j, w j * N.C j := by
  have hi : ∀ i, 3/5 * listCompletion I π₁ i + 2/5 * listCompletion I π₂ i ≤ 9/5 * P.CP i := by
    intro i
    have h1 := ba_bound_G P 1 ⟨one_pos, le_rfl⟩ π₁ hπ₁ i
    have h2 := ba_bound_G P (1/2) ⟨by norm_num, by norm_num⟩ π₂ hπ₂ i
    have hT := ba_idle_nonneg P i
    have hs : ∑ j, (3/5 * baG 1 (P.frac i j) (I.p j) + 2/5 * baG (1/2) (P.frac i j) (I.p j))
        ≤ ∑ j, 9/5 * (P.frac i j * I.p j) := Finset.sum_le_sum fun j _ =>
      baG_two _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j) (I.p_pos j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    rw [ba_CP_decomp P i]
    linarith
  have hN := ba_sum_CP_le w hw P hP N
  calc 3 / 5 * ∑ j, w j * listCompletion I π₁ j + 2 / 5 * ∑ j, w j * listCompletion I π₂ j
      = ∑ j, w j * (3/5 * listCompletion I π₁ j + 2/5 * listCompletion I π₂ j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ ∑ j, w j * (9/5 * P.CP j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j) (hw j).le
    _ = 9/5 * ∑ j, w j * P.CP j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ 9 / 5 * ∑ j, w j * N.C j := by linarith

lemma ba_ii_sum {ι : Type*} {a b : ℝ} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have := IntervalIntegrable.sum s h
  have e : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x; simp [Finset.sum_apply]
  rw [e]; exact this

lemma baG_eq_left {α x p : ℝ} (h : α ≤ x) : baG α x p = (1 + α) * p := by
  unfold baG; rw [if_pos h, if_neg (not_lt.2 h), add_zero]

lemma baG_eq_right {α x p : ℝ} (h : x < α) : baG α x p = x * p := by
  unfold baG; rw [if_neg (not_le.2 h), if_pos h, zero_add]

lemma baG_int (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (x p : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    IntervalIntegrable (fun α => f α * baG α x p) volume 0 1 ∧
    ∫ α in (0:ℝ)..1, f α * baG α x p =
      p * (∫ α in (0:ℝ)..x, f α * (1 + α)) + x * p * ∫ α in x..1, f α := by
  have hf1 : IntervalIntegrable f volume 0 x := hf.mono_set (by
    rw [Set.uIcc_of_le hx0, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hx1)
  have hf2 : IntervalIntegrable f volume x 1 := hf.mono_set (by
    rw [Set.uIcc_of_le hx1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc hx0 le_rfl)
  have hA : IntervalIntegrable (fun α => f α * ((1 + α) * p)) volume 0 x :=
    hf1.mul_continuousOn (by fun_prop)
  have hB : IntervalIntegrable (fun α => f α * (x * p)) volume x 1 := hf2.mul_const _
  have eqA : Set.EqOn (fun α => f α * ((1 + α) * p)) (fun α => f α * baG α x p)
      (Set.uIcc 0 x) := by
    intro α hα; rw [Set.uIcc_of_le hx0] at hα; simp only; rw [baG_eq_left hα.2]
  have eqB : Set.EqOn (fun α => f α * (x * p)) (fun α => f α * baG α x p) (Set.uIoc x 1) := by
    intro α hα; rw [Set.uIoc_of_le hx1] at hα; simp only; rw [baG_eq_right hα.1]
  have hA' := hA.congr (eqA.mono Set.uIoc_subset_uIcc)
  have hB' := hB.congr eqB
  refine ⟨hA'.trans hB', ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hA' hB']
  have i1 : ∫ α in (0:ℝ)..x, f α * baG α x p = ∫ α in (0:ℝ)..x, f α * ((1 + α) * p) :=
    (intervalIntegral.integral_congr eqA).symm
  have i2 : ∫ α in x..1, f α * baG α x p = ∫ α in x..1, f α * (x * p) :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun α hα => (eqB hα).symm))
  rw [i1, i2, intervalIntegral.integral_mul_const]
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_mul_const]
  ring

lemma ba_exp_int1 (x : ℝ) : ∫ α in (0:ℝ)..x, Real.exp α * (1 + α) = x * Real.exp x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun α => α * Real.exp α)]
  · simp
  · intro α _
    have := (hasDerivAt_id α).mul (Real.hasDerivAt_exp α)
    exact this.congr_deriv (by simp; ring)
  · apply Continuous.intervalIntegrable; fun_prop

lemma baG_exp (x p : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IntervalIntegrable (fun α => Real.exp α * baG α x p) volume 0 1 ∧
    ∫ α in (0:ℝ)..1, Real.exp α * baG α x p = Real.exp 1 * (x * p) := by
  obtain ⟨h1, h2⟩ := baG_int Real.exp (Continuous.intervalIntegrable (by fun_prop) _ _) x p hx0 hx1
  refine ⟨h1, ?_⟩
  rw [h2, ba_exp_int1, integral_exp]
  ring

theorem best_alpha_core {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, P.CP j ≤ ∑ j, P'.CP j) :
    ∃ α ∈ Set.Ioc (0 : ℝ) 1, ∀ π : Fin n ≃ Fin n, IsAlphaOrder P α π →
      ∀ N : NonpreemptiveSchedule I,
        ∑ j, listCompletion I π j ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, N.C j := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero
    linarith
  have hc0 : 0 < Real.exp 1 - 1 := by linarith
  set c := Real.exp 1 / (Real.exp 1 - 1) * ∑ i, P.CP i with hc
  set B : ℝ → ℝ := fun α => ∑ i, (P.idle i + ∑ j, baG α (P.frac i j) (I.p j)) with hB
  have hex : ∃ α ∈ Set.Ioc (0 : ℝ) 1, B α ≤ c := by
    by_contra hcon
    push_neg at hcon
    set H : ℝ → ℝ := fun α => ∑ i, (Real.exp α * P.idle i +
      ∑ j, Real.exp α * baG α (P.frac i j) (I.p j)) with hH
    have hHB : ∀ α, Real.exp α * B α = H α := by
      intro α
      simp only [hB, hH, Finset.mul_sum, mul_add]
    have hHi : IntervalIntegrable H volume 0 1 := by
      simp only [hH]
      apply ba_ii_sum
      intro i _
      apply IntervalIntegrable.add
      · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
      · apply ba_ii_sum
        intro j _
        exact (baG_exp _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j)).1
    have hHint : ∫ α in (0:ℝ)..1, H α =
        ∑ i, ((Real.exp 1 - 1) * P.idle i + ∑ j, Real.exp 1 * (P.frac i j * I.p j)) := by
      simp only [hH]
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_add]
        · rw [intervalIntegral.integral_finset_sum]
          · rw [intervalIntegral.integral_mul_const, integral_exp, Real.exp_zero]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact (baG_exp _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j)).2
          · intro j _
            exact (baG_exp _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j)).1
        · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
        · apply ba_ii_sum
          intro j _
          exact (baG_exp _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j)).1
      · intro i _
        apply IntervalIntegrable.add
        · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
        · apply ba_ii_sum
          intro j _
          exact (baG_exp _ _ (ba_frac_nonneg P i j) (ba_frac_le_one P i j)).1
    have hle : ∑ i, ((Real.exp 1 - 1) * P.idle i + ∑ j, Real.exp 1 * (P.frac i j * I.p j))
        ≤ Real.exp 1 * ∑ i, P.CP i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [ba_CP_decomp P i, ← Finset.mul_sum]
      have := ba_idle_nonneg P i
      nlinarith
    have hpos : 0 < ∫ α in (0:ℝ)..1, (H α - c * Real.exp α) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
      · exact hHi.sub ((Continuous.intervalIntegrable (by fun_prop) _ _))
      · intro α hα
        have h1 := hcon α ⟨hα.1, hα.2.le⟩
        rw [← hHB]
        have := Real.exp_pos α
        nlinarith
      · norm_num
    rw [intervalIntegral.integral_sub hHi (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero, hHint] at hpos
    have hce : c * (Real.exp 1 - 1) = Real.exp 1 * ∑ i, P.CP i := by
      rw [hc]; field_simp
    linarith
  obtain ⟨α, hα, hBα⟩ := hex
  refine ⟨α, hα, fun π hπ N => ?_⟩
  have h1 : ∑ j, listCompletion I π j ≤ B α :=
    Finset.sum_le_sum fun i _ => ba_bound_G P α hα π hπ i
  have h2 : ∑ i, P.CP i ≤ ∑ j, N.C j :=
    (hP (baOfN N)).trans (Finset.sum_le_sum fun j _ => baOfN_CP N j)
  have h3 : 0 < Real.exp 1 / (Real.exp 1 - 1) := div_pos (by linarith) hc0
  calc ∑ j, listCompletion I π j ≤ c := h1.trans hBα
    _ ≤ _ := by rw [hc]; exact mul_le_mul_of_nonneg_left h2 h3.le

end AvgCompletionSched.BestAlpha

open AvgCompletionSched.BestAlpha


theorem solution {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, P.CP j ≤ ∑ j, P'.CP j) :
    ∃ α ∈ Set.Ioc (0 : ℝ) 1, ∀ π : Fin n ≃ Fin n, IsAlphaOrder P α π →
      ∀ N : NonpreemptiveSchedule I,
        ∑ j, listCompletion I π j ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, N.C j := by
  exact best_alpha_core P hP
