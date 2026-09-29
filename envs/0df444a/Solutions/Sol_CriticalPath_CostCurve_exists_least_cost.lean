-- Prove2me | solution 1 for CriticalPath.CostCurve.exists_least_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:35:03.177091+00:00
-- url     : https://prove2.me/submissions/776c889b-f0d5-4216-92cd-efcf382235a6

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule



namespace CriticalPath.CostCurve

variable {n : ℕ}

lemma earliest_eq' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin (n+1)) :
    earliest N y j = if h : (preds N j).Nonempty then
      (preds N j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun i => y i.1 j + earliest N y i.1)
    else 0 := by
  rw [earliest]

lemma mem_preds' (N : ProjectNetwork n) {i j : Fin (n+1)} (h : (i, j) ∈ N.P) : i ∈ preds N j := by
  simp [preds, N.label_lt _ h, h]

lemma le_earliest' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) {i j : Fin (n+1)}
    (h : (i, j) ∈ N.P) : y i j + earliest N y i ≤ earliest N y j := by
  have hm := mem_preds' N h
  have hne : (preds N j).Nonempty := ⟨i, hm⟩
  rw [earliest_eq' N y j, dif_pos hne]
  exact Finset.le_sup' (fun i : (preds N j) => y i.1 j + earliest N y i.1) (Finset.mem_attach _ ⟨i, hm⟩)

lemma earliest_zero' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    earliest N y 0 = 0 := by
  rw [earliest_eq', dif_neg]
  rintro ⟨i, hi⟩
  simp [preds] at hi

lemma earliest_le_of' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n+1) → ℝ) (hy : ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1) (ht : ∀ j, t 0 ≤ t j) :
    ∀ j, earliest N y j ≤ t j - t 0 := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  rw [earliest_eq']
  split_ifs with hne
  · apply Finset.sup'_le
    rintro ⟨i, hi⟩ _
    have hi' := Finset.mem_filter.mp hi
    have h1 := ih i hi'.2.1
    have h2 := hy (i, j) hi'.2.2
    simp only at h2 ⊢
    linarith
  · linarith [ht j]

lemma earliest_mono' (N : ProjectNetwork n) (y y' : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hy : ∀ e ∈ N.P, y e.1 e.2 ≤ y' e.1 e.2) : ∀ j, earliest N y j ≤ earliest N y' j := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  rw [earliest_eq' N y j]
  split_ifs with hne
  · apply Finset.sup'_le
    rintro ⟨i, hi⟩ _
    have hi' := Finset.mem_filter.mp hi
    have h1 := ih i hi'.2.1
    have h2 := hy (i, j) hi'.2.2
    have h3 := le_earliest' N y' hi'.2.2
    simp only at h2 ⊢
    linarith
  · rw [earliest_eq' N y' j, dif_neg hne]

lemma earliest_continuous' (N : ProjectNetwork n) (Y : ℝ → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hY : ∀ i j, Continuous (fun s => Y s i j)) : ∀ j, Continuous (fun s => earliest N (Y s) j) := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  simp_rw [earliest_eq' N _ j]
  split_ifs with hne
  · apply Continuous.finset_sup'_apply
    rintro ⟨i, hi⟩ _
    exact (hY i j).add (ih i (Finset.mem_filter.mp hi).2.1)
  · exact continuous_const

lemma sched_mono' {N : ProjectNetwork n} (J : JobData N) {lam : ℝ} {y t}
    (h : IsSchedule J lam y t) {a b : Fin (n+1)}
    (hab : Relation.ReflTransGen (fun i j => (i, j) ∈ N.P) a b) : t a ≤ t b := by
  induction hab with
  | refl => exact le_rfl
  | tail _ he ih =>
    have h1 := h.2.1 _ he
    have h2 := (h.1 _ he).1
    have h3 := J.crash_nonneg _ he
    simp only at h1 h2 h3
    linarith

lemma sched_bounds' {N : ProjectNetwork n} (J : JobData N) {lam : ℝ} {y t}
    (h : IsSchedule J lam y t) (j : Fin (n+1)) : 0 ≤ t j ∧ t j ≤ lam := by
  have h1 := sched_mono' J h (N.origin_precedes j)
  have h2 := sched_mono' J h (N.terminus_follows j)
  rw [h.2.2.1] at h1; rw [h.2.2.2] at h2
  exact ⟨h1, h2⟩

lemma last_ne_zero' (N : ProjectNetwork n) : (Fin.last n) ≠ 0 := by
  have := N.one_le
  intro h
  have := congrArg Fin.val h
  simp at this; omega

lemma feasible_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    feasibleDurations J = Set.Ici (earliest N J.d (Fin.last n)) := by
  ext lam
  constructor
  · rintro ⟨y, t, h⟩
    have hy : ∀ e ∈ N.P, J.d e.1 e.2 ≤ t e.2 - t e.1 := fun e he =>
      le_trans (h.1 e he).1 (h.2.1 e he)
    have := earliest_le_of' N J.d t hy (fun j => by rw [h.2.2.1]; exact (sched_bounds' J h j).1)
      (Fin.last n)
    rw [h.2.2.1, h.2.2.2] at this
    simp only [Set.mem_Ici]; linarith
  · intro hl
    simp only [Set.mem_Ici] at hl
    refine ⟨J.d, fun j => if j = Fin.last n then lam else earliest N J.d j, ?_, ?_, ?_, ?_⟩
    · intro e he; exact ⟨le_rfl, J.crash_le_normal e he⟩
    · intro e he
      have hlt := N.label_lt e he
      have h1 : e.1 ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last _))
      have h2 := le_earliest' N J.d (i := e.1) (j := e.2) he
      simp only [h1, if_false]
      split_ifs with h3
      · rw [h3] at h2 ⊢; linarith
      · linarith
    · simp [Ne.symm (last_ne_zero' N), earliest_zero']
    · simp

lemma cost_mono' {N : ProjectNetwork n} (J : JobData N) (y y' : Fin (n + 1) → Fin (n + 1) → ℝ)
    (h : ∀ e ∈ N.P, y e.1 e.2 ≤ y' e.1 e.2) : projectCost J y' ≤ projectCost J y := by
  unfold projectCost
  apply Finset.sum_le_sum
  intro e he
  have := mul_le_mul_of_nonpos_left (h e he) (J.slope_nonpos e he)
  linarith

lemma all_normal_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    IsOptimalSchedule J (earliest N J.D (Fin.last n)) J.D (earliest N J.D) := by
  refine ⟨⟨fun e he => ⟨J.crash_le_normal e he, le_rfl⟩, fun e he => ?_, earliest_zero' N _, rfl⟩, ?_⟩
  · have := le_earliest' N J.D (i := e.1) (j := e.2) he
    linarith
  · intro y' t' h
    exact cost_mono' J y' J.D (fun e he => (h.1 e he).2)

noncomputable def trunc' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if (i, j) ∈ N.P then y i j else 0

lemma trunc_sched' {N : ProjectNetwork n} (J : JobData N) {lam : ℝ} {y t}
    (h : IsSchedule J lam y t) : IsSchedule J lam (trunc' N y) t := by
  refine ⟨fun e he => ?_, fun e he => ?_, h.2.2.1, h.2.2.2⟩
  · simp only [trunc', Prod.mk.eta, if_pos he]; exact h.1 e he
  · simp only [trunc', Prod.mk.eta, if_pos he]; exact h.2.1 e he

lemma trunc_cost' {N : ProjectNetwork n} (J : JobData N) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    projectCost J (trunc' N y) = projectCost J y := by
  unfold projectCost
  apply Finset.sum_congr rfl
  intro e he
  simp only [trunc', Prod.mk.eta, if_pos he]

lemma exists_opt' {N : ProjectNetwork n} (J : JobData N) (lam : ℝ) (hl : lam ∈ feasibleDurations J) :
    ∃ y t, IsOptimalSchedule J lam y t := by
  classical
  let lo : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => if (i, j) ∈ N.P then J.d i j else 0
  let hi : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => if (i, j) ∈ N.P then J.D i j else 0
  let B : Set ((Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    (Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (lo i j) (hi i j)) ×ˢ
      (Set.univ.pi fun _ => Set.Icc 0 lam)
  let S : Set ((Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    {p | IsSchedule J lam p.1 p.2}
  have hS : IsClosed S := by
    have hEq : S = (⋂ e ∈ N.P, ({p : (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) |
          J.d e.1 e.2 ≤ p.1 e.1 e.2} ∩ {p | p.1 e.1 e.2 ≤ J.D e.1 e.2})) ∩
        (⋂ e ∈ N.P, {p : (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) |
          p.1 e.1 e.2 ≤ p.2 e.2 - p.2 e.1}) ∩
        ({p : (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) | p.2 0 = 0} ∩
          {p | p.2 (Fin.last n) = lam}) := by
      ext p; simp [S, IsSchedule, and_assoc, forall_and]
    rw [hEq]
    refine ((isClosed_biInter fun e _ => (isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter
      (isClosed_biInter fun e _ => isClosed_le ?_ ?_)).inter
      ((isClosed_eq ?_ ?_).inter (isClosed_eq ?_ ?_))
    all_goals fun_prop
  have hB : IsCompact B :=
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hK := hB.inter_right hS
  have hinB : ∀ y t, IsSchedule J lam y t → (trunc' N y, t) ∈ B ∩ S := by
    intro y t h
    refine ⟨⟨?_, ?_⟩, trunc_sched' J h⟩
    · intro i _ j _
      simp only [trunc', lo, hi]
      split_ifs with hij
      · exact h.1 (i, j) hij
      · simp
    · intro j _
      exact sched_bounds' J h j
  obtain ⟨y0, t0, h0⟩ := hl
  have hne : (B ∩ S).Nonempty := ⟨_, hinB y0 t0 h0⟩
  have hc : Continuous fun p : ((Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) =>
      projectCost J p.1 := by
    unfold projectCost
    fun_prop
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨p.1, p.2, hp.2, fun y' t' h' => ?_⟩
  have := hmin (hinB y' t' h')
  simp only [Set.mem_setOf_eq] at this
  rw [trunc_cost'] at this
  exact this

lemma least_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    ∀ lam ∈ feasibleDurations J, ∃ c : ℝ, IsLeast (costSet J lam) c := by
  intro lam hl
  obtain ⟨y, t, h, hmin⟩ := exists_opt' J lam hl
  refine ⟨projectCost J y, ⟨y, t, h, rfl⟩, ?_⟩
  rintro c ⟨y', t', h', rfl⟩
  exact hmin y' t' h'

lemma opt_earliest_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (lam : ℝ)
    (hlo : earliest N J.d (Fin.last n) ≤ lam) (hhi : lam ≤ earliest N J.D (Fin.last n)) :
    ∃ (y : Fin (n + 1) → Fin (n + 1) → ℝ) (t : Fin (n + 1) → ℝ),
      IsOptimalSchedule J lam y t ∧ earliest N y (Fin.last n) = lam := by
  have hl : lam ∈ feasibleDurations J := by rw [feasible_core]; exact hlo
  obtain ⟨y, t, h, hmin⟩ := exists_opt' J lam hl
  let Y : ℝ → Fin (n + 1) → Fin (n + 1) → ℝ := fun s i j => y i j + s * (J.D i j - y i j)
  let f : ℝ → ℝ := fun s => earliest N (Y s) (Fin.last n)
  have hf : Continuous f := earliest_continuous' N Y (fun i j => by fun_prop) _
  have hf0 : f 0 ≤ lam := by
    have hY : Y 0 = y := by funext i j; simp [Y]
    have := earliest_le_of' N y t (fun e he => h.2.1 e he)
      (fun j => by rw [h.2.2.1]; exact (sched_bounds' J h j).1) (Fin.last n)
    rw [h.2.2.1, h.2.2.2] at this
    simp only [f, hY]; linarith
  have hf1 : lam ≤ f 1 := by
    have hY : Y 1 = J.D := by funext i j; simp [Y]
    simp only [f, hY]; exact hhi
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hf.continuousOn ⟨hf0, hf1⟩
  have hyle : ∀ e ∈ N.P, y e.1 e.2 ≤ Y s e.1 e.2 := by
    intro e he
    have := (h.1 e he).2
    simp only [Y]; nlinarith
  refine ⟨Y s, earliest N (Y s), ⟨⟨fun e he => ⟨?_, ?_⟩, fun e he => ?_, earliest_zero' N _, hs⟩,
    fun y' t' h' => le_trans (cost_mono' J y (Y s) hyle) (hmin y' t' h')⟩, hs⟩
  · exact le_trans (h.1 e he).1 (hyle e he)
  · have := (h.1 e he).2
    simp only [Y]; nlinarith
  · have := le_earliest' N (Y s) (i := e.1) (j := e.2) he
    linarith

end CriticalPath.CostCurve

open CriticalPath.CostCurve


theorem solution {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    ∀ lam ∈ feasibleDurations J, ∃ c : ℝ, IsLeast (costSet J lam) c := by
  exact least_core N J
