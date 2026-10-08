-- Prove2me | solution 1 for FlowJobShop.PairGroups.algorithmH_finishTime_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:18:25.992524+00:00
-- url     : https://prove2.me/submissions/f62f3b3d-e811-4d97-a7a3-48e05e173e0e

import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH



namespace FlowJobShop.PairGroups

open FlowShop

lemma pg_fold_le_iff {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) (c x : ℝ) :
    s.fold max c f ≤ x ↔ c ≤ x ∧ ∀ a ∈ s, f a ≤ x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha, max_le_iff, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    tauto

lemma pg_le_fold {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) (c : ℝ) :
    c ≤ s.fold max c f ∧ ∀ a ∈ s, f a ≤ s.fold max c f :=
  (pg_fold_le_iff s f c _).1 le_rfl

lemma pg_ft_nonneg {m n : ℕ} (F : FlowShop m n) (s : Fin m → Fin n → ℝ) :
    0 ≤ F.finishTime s := (pg_le_fold _ _ _).1

lemma pg_le_ft {m n : ℕ} (F : FlowShop m n) (s : Fin m → Fin n → ℝ) (j : Fin m) (i : Fin n) :
    s j i + F.t j i ≤ F.finishTime s :=
  (pg_le_fold (Finset.univ : Finset (Fin m × Fin n)) (fun p => s p.1 p.2 + F.t p.1 p.2) 0).2
    (j, i) (Finset.mem_univ _)

lemma pg_ft_le {m n : ℕ} (F : FlowShop m n) (s : Fin m → Fin n → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (h : ∀ j i, s j i + F.t j i ≤ x) : F.finishTime s ≤ x := by
  unfold finishTime
  rw [pg_fold_le_iff]
  exact ⟨hx, fun p _ => h p.1 p.2⟩

lemma pg_cont_fold {α X : Type*} [DecidableEq α] [TopologicalSpace X] (s : Finset α)
    (f : α → X → ℝ) (hf : ∀ a, Continuous (f a)) (c : ℝ) :
    Continuous (fun x => s.fold max c (fun a => f a x)) := by
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact (hf a).max ih

lemma pg_cont_ft {m n : ℕ} (F : FlowShop m n) :
    Continuous (fun s : Fin m → Fin n → ℝ => F.finishTime s) := by
  unfold finishTime
  refine pg_cont_fold (Finset.univ : Finset (Fin m × Fin n))
    (fun p (s : Fin m → Fin n → ℝ) => s p.1 p.2 + F.t p.1 p.2) (fun p => ?_) 0
  fun_prop

lemma pg_exists_feasible {m n : ℕ} (F : FlowShop m n) : ∃ s, F.IsFeasible s := by
  set T : ℝ := (∑ p : Fin m × Fin n, F.t p.1 p.2) + 1 with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ ∑ p : Fin m × Fin n, F.t p.1 p.2 := Finset.sum_nonneg (fun p _ => F.t_nonneg _ _)
    linarith
  have htT : ∀ j i, F.t j i ≤ T := by
    intro j i
    have := Finset.single_le_sum (f := fun p : Fin m × Fin n => F.t p.1 p.2)
      (fun p _ => F.t_nonneg _ _) (Finset.mem_univ (j, i))
    simp only at this
    linarith
  refine ⟨fun j i => (((i.val * m + j.val : ℕ)) : ℝ) * T, ?_, ?_, ?_⟩
  · intro j i; positivity
  · intro i j j' hj
    have h : (((i.val * m + j'.val : ℕ)) : ℝ) = (((i.val * m + j.val : ℕ)) : ℝ) + 1 := by
      rw [← hj]; push_cast; ring
    simp only
    rw [h]
    have := htT j i
    nlinarith
  · intro j i i' hne _ _
    have hj := j.isLt
    have key : ∀ a b : Fin n, a.val < b.val →
        (((a.val * m + j.val : ℕ)) : ℝ) * T + F.t j a ≤ (((b.val * m + j.val : ℕ)) : ℝ) * T := by
      intro a b hab
      have h1 : a.val * m + j.val + 1 ≤ b.val * m + j.val := by
        have : (a.val + 1) * m ≤ b.val * m := Nat.mul_le_mul_right _ hab
        nlinarith
      have h2 : (((a.val * m + j.val : ℕ)) : ℝ) + 1 ≤ (((b.val * m + j.val : ℕ)) : ℝ) := by
        exact_mod_cast h1
      have := htT j a
      nlinarith
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · left; exact key i i' h
    · right; exact key i' i h

lemma pg_closed {m n : ℕ} (F : FlowShop m n) :
    IsClosed {s : Fin m → Fin n → ℝ | F.IsFeasible s} := by
  have hc : ∀ j i, Continuous (fun s : Fin m → Fin n → ℝ => s j i) :=
    fun j i => (continuous_apply i).comp (continuous_apply j)
  unfold IsFeasible
  simp only [Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun i =>
    isClosed_le continuous_const (hc j i)) (IsClosed.inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun j' => ?_)
    (isClosed_iInter fun j => isClosed_iInter fun i => isClosed_iInter fun i' => ?_))
  · exact isClosed_iInter fun _ => isClosed_le ((hc j i).add continuous_const) (hc j' i)
  · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      IsClosed.union (isClosed_le ((hc j i).add continuous_const) (hc j i'))
        (isClosed_le ((hc j i').add continuous_const) (hc j i))

theorem pg_exists_opt {m n : ℕ} (F : FlowShop m n) : ∃ ρ, F.IsOptimal ρ := by
  obtain ⟨s0, hs0⟩ := pg_exists_feasible F
  set T0 := F.finishTime s0 with hT0
  set K : Set (Fin m → Fin n → ℝ) := {s | F.IsFeasible s ∧ F.finishTime s ≤ T0} with hK
  have hKc : IsCompact K := by
    have hcl : IsClosed K := by
      refine (pg_closed F).inter ?_
      exact isClosed_le (pg_cont_ft F) continuous_const
    have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ
        (fun _ : Fin n => Set.Icc (0:ℝ) T0))) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    refine hbox.of_isClosed_subset hcl ?_
    intro s ⟨hf, hle⟩ j _ i _
    refine ⟨hf.1 j i, ?_⟩
    have := pg_le_ft F s j i
    have := F.t_nonneg j i
    linarith
  obtain ⟨ρ, hρ, hmin⟩ := hKc.exists_isMinOn ⟨s0, hs0, le_rfl⟩ (pg_cont_ft F).continuousOn
  refine ⟨ρ, hρ.1, fun s' hs' => ?_⟩
  by_cases h : F.finishTime s' ≤ T0
  · exact hmin ⟨hs', h⟩
  · push_neg at h
    exact hρ.2.trans h.le

lemma pg_restrict {m n : ℕ} (F : FlowShop m n) (g : Fin ((m + 1) / 2))
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    (F.group g).IsFeasible (fun k i => τ (groupProc g k) i) := by
  obtain ⟨h1, h2, h3⟩ := hτ
  refine ⟨fun k i => h1 _ _, ?_, ?_⟩
  · intro i k k' hk
    exact h2 i (groupProc g k) (groupProc g k') (by simp only [groupProc]; omega)
  · intro k i i' hii ht ht'
    exact h3 (groupProc g k) i i' hii ht ht'

lemma pg_group_le {m n : ℕ} (F : FlowShop m n) (g : Fin ((m + 1) / 2))
    (ρ : Fin (groupSize m g) → Fin n → ℝ) (hρ : (F.group g).IsOptimal ρ)
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    (F.group g).finishTime ρ ≤ F.finishTime τ := by
  refine (hρ.2 _ (pg_restrict F g τ hτ)).trans ?_
  refine pg_ft_le _ _ _ (pg_ft_nonneg _ _) fun k i => ?_
  exact pg_le_ft F τ (groupProc g k) i

theorem pg_group_opt_le {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsOptimal (R g))
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    (Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)) ≤ F.finishTime τ := by
  rw [pg_fold_le_iff]
  exact ⟨pg_ft_nonneg _ _, fun g _ => pg_group_le F g _ (hR g) τ hτ⟩

lemma pg_proc_eq {m : ℕ} (j : Fin m) : groupProc (groupOf j) (posInGroup j) = j := by
  apply Fin.ext
  simp only [groupProc, groupOf, posInGroup]
  omega

lemma pg_offset_nonneg {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) (g) :
    0 ≤ F.offset R g :=
  Finset.sum_nonneg fun h _ => pg_ft_nonneg _ _

lemma pg_offset_add {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) (g) :
    F.offset R g + (F.group g).finishTime (R g) ≤ ∑ h, (F.group h).finishTime (R h) := by
  unfold offset
  have : (∑ h ∈ Finset.univ.filter (fun h : Fin ((m + 1) / 2) => h < g),
        (F.group h).finishTime (R h)) + (F.group g).finishTime (R g) =
      ∑ h ∈ insert g (Finset.univ.filter (fun h : Fin ((m + 1) / 2) => h < g)),
        (F.group h).finishTime (R h) := by
    rw [Finset.sum_insert (by simp), add_comm]
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun h _ _ => pg_ft_nonneg _ _)

lemma pg_offset_mono {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) {g g' : Fin ((m + 1) / 2)}
    (h : g < g') :
    F.offset R g + (F.group g).finishTime (R g) ≤ F.offset R g' := by
  unfold offset
  have : (∑ h ∈ Finset.univ.filter (fun h : Fin ((m + 1) / 2) => h < g),
        (F.group h).finishTime (R h)) + (F.group g).finishTime (R g) =
      ∑ h ∈ insert g (Finset.univ.filter (fun h : Fin ((m + 1) / 2) => h < g)),
        (F.group h).finishTime (R h) := by
    rw [Finset.sum_insert (by simp), add_comm]
  rw [this]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => pg_ft_nonneg _ _)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with rfl | hx
  · exact h
  · exact hx.trans h

lemma pg_R_congr {m n : ℕ}
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) {g g' : Fin ((m + 1) / 2)}
    (hg : g = g') {k : Fin (groupSize m g)} {k' : Fin (groupSize m g')} (hk : k.val = k'.val)
    (i : Fin n) : R g k i = R g' k' i := by
  subst hg; rw [Fin.ext hk]

lemma pg_t_eq {m n : ℕ} (F : FlowShop m n) (j : Fin m) (i : Fin n) :
    (F.group (groupOf j)).t (posInGroup j) i = F.t j i := by
  show F.t (groupProc (groupOf j) (posInGroup j)) i = _
  rw [pg_proc_eq]

lemma pg_elem_le {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) (j : Fin m) (i : Fin n) :
    R (groupOf j) (posInGroup j) i + F.t j i ≤ (F.group (groupOf j)).finishTime (R (groupOf j)) := by
  have := pg_le_ft (F.group (groupOf j)) (R (groupOf j)) (posInGroup j) i
  rwa [pg_t_eq] at this

theorem pg_feasible {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsFeasible (R g)) :
    F.IsFeasible (F.algorithmH R) := by
  refine ⟨fun j i => ?_, fun i j j' hj => ?_, fun j i i' hii ht ht' => ?_⟩
  · simp only [algorithmH]
    exact add_nonneg ((hR _).1 _ _) (pg_offset_nonneg F R _)
  · simp only [algorithmH]
    have hj2 : j.val + 1 = j'.val := hj
    by_cases hg : groupOf j = groupOf j'
    · have h1 : j.val / 2 = j'.val / 2 := congrArg Fin.val hg
      let k' : Fin (groupSize m (groupOf j)) :=
        ⟨(posInGroup j').val, by have := j'.isLt; simp only [posInGroup, groupSize, groupOf]; omega⟩
      have hk : (posInGroup j).val + 1 = k'.val := by
        simp only [posInGroup, k']; omega
      have h := (hR (groupOf j)).2.1 i (posInGroup j) k' hk
      have e1 : (F.group (groupOf j)).t (posInGroup j) i = F.t j i := pg_t_eq F j i
      rw [e1] at h
      have e2 := pg_R_congr R hg (k := k') (k' := posInGroup j') (rfl) i
      have e3 : F.offset R (groupOf j) = F.offset R (groupOf j') := by rw [hg]
      rw [← e2, ← e3]
      linarith
    · have hlt : groupOf j < groupOf j' := by
        show j.val / 2 < j'.val / 2
        have : j.val / 2 ≠ j'.val / 2 := fun h => hg (Fin.ext h)
        omega
      have h1 := pg_elem_le F R j i
      have h2 := pg_offset_mono F R hlt
      have h3 := (hR (groupOf j')).1 (posInGroup j') i
      linarith
  · simp only [algorithmH]
    have h := (hR (groupOf j)).2.2 (posInGroup j) i i' hii (by rwa [pg_t_eq]) (by rwa [pg_t_eq])
    rw [pg_t_eq, pg_t_eq] at h
    rcases h with h | h
    · left; linarith
    · right; linarith

theorem pg_alg_le {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsFeasible (R g)) :
    F.finishTime (F.algorithmH R) ≤ ∑ g, (F.group g).finishTime (R g) ∧
    ∑ g, (F.group g).finishTime (R g) ≤
      (((m + 1) / 2 : ℕ) : ℝ) * (Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)) := by
  constructor
  · refine pg_ft_le _ _ _ (Finset.sum_nonneg fun h _ => pg_ft_nonneg _ _) fun j i => ?_
    simp only [algorithmH]
    have h1 := pg_elem_le F R j i
    have h2 := pg_offset_add F R (groupOf j)
    linarith
  · have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin ((m + 1) / 2)))
      (fun g => (F.group g).finishTime (R g))
      ((Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)))
      (fun g hg => (pg_le_fold (Finset.univ : Finset (Fin ((m + 1) / 2)))
        (fun g => (F.group g).finishTime (R g)) 0).2 g hg)
    simpa [nsmul_eq_mul] using this

theorem pg_lemma11 {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsOptimal (R g))
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    F.finishTime (F.algorithmH R) ≤ (((m + 1) / 2 : ℕ) : ℝ) * F.finishTime τ := by
  obtain ⟨h1, h2⟩ := pg_alg_le F R (fun g => (hR g).1)
  have h3 := pg_group_opt_le F R hR τ hτ
  have h4 : (0:ℝ) ≤ (((m + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h3 h4
  linarith

end FlowJobShop.PairGroups

open FlowJobShop.PairGroups


theorem solution {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsFeasible (R g)) :
    F.finishTime (F.algorithmH R) ≤ ∑ g, (F.group g).finishTime (R g) ∧
    ∑ g, (F.group g).finishTime (R g) ≤
      (((m + 1) / 2 : ℕ) : ℝ) * (Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)) := by
  exact pg_alg_le F R hR
