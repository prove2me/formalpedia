-- Prove2me | solution 1 for CriticalPath.CostCurve.project_cost_curve
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:46:26.361623+00:00
-- url     : https://prove2.me/submissions/a48a703a-da54-4867-8ecf-de4172c03414

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule
import Definitions.Def_CriticalPath_CostCurve_IsPiecewiseLinearOn



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



lemma root_between' (α γ μ x : ℝ) (h1 : α * μ + γ ≤ 0) (h2 : 0 < α * x + γ) :
    (μ ≤ -γ / α ∧ -γ / α < x) ∨ (x < -γ / α ∧ -γ / α ≤ μ) := by
  have hα : α ≠ 0 := by
    rintro rfl; linarith
  have hρ : α * (-γ / α) + γ = 0 := by field_simp; ring
  set ρ := -γ / α
  rcases lt_or_gt_of_ne hα with h | h
  · right; constructor <;> nlinarith
  · left; constructor <;> nlinarith

lemma assemble' (L0 : ℝ) (C : ℝ → ℝ) (τ ι : Type) [Fintype τ] [Fintype ι]
    (a b : τ → ℝ) (α γ : τ → ι → ℝ)
    (H1 : ∀ x, L0 ≤ x → ∃ T, (∀ i, α T i * x + γ T i ≤ 0) ∧ C x = a T + b T * x)
    (H2 : ∀ T x, L0 ≤ x → (∀ i, α T i * x + γ T i ≤ 0) → C x ≤ a T + b T * x)
    (hconv : ConvexOn ℝ (Set.Ici L0) C) : IsPiecewiseLinearOn C (Set.Ici L0) := by
  classical
  let R : Finset ℝ := insert L0 ((Finset.univ.image fun p : τ × ι => -(γ p.1 p.2) / α p.1 p.2) ∪
    (Finset.univ.image fun p : τ × τ => -(a p.1 - a p.2) / (b p.1 - b p.2)))
  let R' := R.filter (L0 ≤ ·)
  have hL0 : L0 ∈ R' := Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, le_rfl⟩
  have hpos : 0 < R'.card := Finset.card_pos.mpr ⟨L0, hL0⟩
  set m := R'.card - 1 with hm
  have hcard : R'.card = m + 1 := by omega
  let β : Fin (m + 1) → ℝ := fun k => R'.orderEmbOfFin hcard k
  have hβmono : StrictMono β := (R'.orderEmbOfFin hcard).strictMono
  have hβmem : ∀ k, β k ∈ R' := fun k => R'.orderEmbOfFin_mem hcard k
  have hβge : ∀ k, L0 ≤ β k := fun k => (Finset.mem_filter.mp (hβmem k)).2
  have hβ0 : β 0 ≤ L0 := by
    have : β 0 = R'.min' ⟨L0, hL0⟩ := Finset.orderEmbOfFin_zero hcard (Nat.succ_pos _)
    rw [this]; exact R'.min'_le _ hL0
  let InOpen : Fin (m + 1) → ℝ → Prop := fun k x => β k < x ∧ ∀ k', k < k' → x < β k'
  let Cl : Fin (m + 1) → ℝ → Prop := fun k x => β k ≤ x ∧ ∀ k', k < k' → x ≤ β k'
  have K1 : ∀ k r, r ∈ R → ¬ InOpen k r := by
    intro k r hr ⟨h1, h2⟩
    by_cases hr0 : L0 ≤ r
    · have : r ∈ R' := Finset.mem_filter.mpr ⟨hr, hr0⟩
      have : r ∈ Set.range β := by
        change r ∈ Set.range (R'.orderEmbOfFin hcard)
        rw [Finset.range_orderEmbOfFin]; exact this
      obtain ⟨j, rfl⟩ := this
      have := h2 j (hβmono.lt_iff_lt.mp h1)
      exact lt_irrefl _ this
    · linarith [hβge k]
  have seg : ∀ k μ x ρ, InOpen k μ → Cl k x → ((μ ≤ ρ ∧ ρ < x) ∨ (x < ρ ∧ ρ ≤ μ)) → InOpen k ρ := by
    intro k μ x ρ hμ hx hρ
    rcases hρ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hμ.1 h1, fun k' hk' => lt_of_lt_of_le h2 (hx.2 k' hk')⟩
    · exact ⟨lt_of_le_of_lt hx.1 h1, fun k' hk' => lt_of_le_of_lt h2 (hμ.2 k' hk')⟩
  have same : ∀ k μ x (A G : ℝ), InOpen k μ → Cl k x → -G / A ∈ R → A * μ + G ≤ 0 →
      A * x + G ≤ 0 := by
    intro k μ x A G hμ hx hR h1
    by_contra h2
    push_neg at h2
    exact K1 k _ hR (seg k μ x _ hμ hx (root_between' A G μ x h1 h2))
  have hRq : ∀ T i, -(γ T i) / α T i ∈ R := by
    intro T i
    apply Finset.mem_insert_of_mem; apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(T, i), Finset.mem_univ _, rfl⟩
  have hRd : ∀ T T', -(a T - a T') / (b T - b T') ∈ R := by
    intro T T'
    apply Finset.mem_insert_of_mem; apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(T, T'), Finset.mem_univ _, rfl⟩
  -- the midpoint of each piece
  have hmid : ∀ k : Fin (m + 1), ∃ μ, InOpen k μ := by
    intro k
    by_cases hk : (k : ℕ) < m
    · let k1 : Fin (m + 1) := ⟨k + 1, by omega⟩
      have hkk1 : k < k1 := by rw [Fin.lt_iff_val_lt_val]; show (k : ℕ) < k + 1; omega
      refine ⟨(β k + β k1) / 2, ?_, ?_⟩
      · linarith [hβmono hkk1]
      · intro k' hk'
        have : k1 ≤ k' := by rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hk'; show (k : ℕ) + 1 ≤ k'; omega
        linarith [hβmono hkk1, hβmono.monotone this]
    · refine ⟨β k + 1, by linarith, ?_⟩
      intro k' hk'
      exfalso
      have := k'.isLt
      rw [Fin.lt_iff_val_lt_val] at hk'
      omega
  choose μ hμ using hmid
  have hμL : ∀ k, L0 ≤ μ k := fun k => le_trans (hβge k) (hμ k).1.le
  choose Tk hTk using fun k => H1 (μ k) (hμL k)
  refine ⟨m, β, fun k => b (Tk k), fun k => a (Tk k), hβmono, fun x hx => le_trans hβ0 hx, ?_⟩
  intro k x hxS hkx hxk
  have hxS' : L0 ≤ x := hxS
  have hCl : Cl k x := ⟨hkx, hxk⟩
  set T := Tk k
  -- membership in Λ_T for points of the closed piece
  have hmem : ∀ y, Cl k y → ∀ i, α T i * y + γ T i ≤ 0 := fun y hy i =>
    same k (μ k) y _ _ (hμ k) hy (hRq T i) ((hTk k).1 i)
  have hopen : ∀ y, InOpen k y → C y = a T + b T * y := by
    intro y hy
    have hyL : L0 ≤ y := le_trans (hβge k) hy.1.le
    have hyCl : Cl k y := ⟨hy.1.le, fun k' hk' => (hy.2 k' hk').le⟩
    have hμCl : Cl k (μ k) := ⟨(hμ k).1.le, fun k' hk' => ((hμ k).2 k' hk').le⟩
    obtain ⟨T', hT'1, hT'2⟩ := H1 y hyL
    have hle := H2 T y hyL (hmem y hyCl)
    have hμT' : ∀ i, α T' i * μ k + γ T' i ≤ 0 := fun i =>
      same k y (μ k) _ _ hy hμCl (hRq T' i) (hT'1 i)
    have h3 := H2 T' (μ k) (hμL k) hμT'
    have h4 := (hTk k).2
    -- compare the two affine functions
    have h5 : (b T - b T') * y + (a T - a T') ≤ 0 :=
      same k (μ k) y _ _ (hμ k) hyCl (hRd T T') (by rw [h4] at h3; linarith)
    linarith
  by_cases hxo : InOpen k x
  · exact (hopen x hxo).trans (by ring)
  · have hne : x ≠ μ k := by rintro rfl; exact hxo (hμ k)
    have hp : InOpen k ((x + μ k) / 2) := by
      apply seg k (μ k) x _ (hμ k) hCl
      rcases lt_or_gt_of_ne hne with h | h
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    have hc1 := hopen _ hp
    have hc2 := (hTk k).2
    have hconv2 := hconv.2 hxS (show μ k ∈ Set.Ici L0 from hμL k)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) + 1/2 = 1)
    simp only [smul_eq_mul] at hconv2
    have hp' : 1 / 2 * x + 1 / 2 * μ k = (x + μ k) / 2 := by ring
    rw [hp', hc1, hc2] at hconv2
    have hle := H2 T x hxS' (hmem x hCl)
    change C x = b T * x + a T
    linarith

lemma vertex_exists' {V : Type} [AddCommGroup V] [Module ℝ V] {ι : Type} [Fintype ι]
    (g : ι → V →ₗ[ℝ] ℝ) (r : ι → ℝ) (φ : V →ₗ[ℝ] ℝ)
    (hray : ∀ x, (∀ i, g i x ≤ r i) → ∀ v, v ≠ 0 → ∃ s : ℝ, 0 < s ∧ ¬ ∀ i, g i (x + s • v) ≤ r i)
    (x0 : V) (hx0 : ∀ i, g i x0 ≤ r i) (hopt0 : ∀ x', (∀ i, g i x' ≤ r i) → φ x0 ≤ φ x') :
    ∃ x, (∀ i, g i x ≤ r i) ∧ (∀ x', (∀ i, g i x' ≤ r i) → φ x ≤ φ x') ∧
      ∀ v, (∀ i, g i x = r i → g i v = 0) → v = 0 := by
  classical
  suffices H : ∀ N, ∀ x, (∀ i, g i x ≤ r i) → (∀ x', (∀ i, g i x' ≤ r i) → φ x ≤ φ x') →
      (Finset.univ.filter fun i => g i x < r i).card = N →
      ∃ x, (∀ i, g i x ≤ r i) ∧ (∀ x', (∀ i, g i x' ≤ r i) → φ x ≤ φ x') ∧
        ∀ v, (∀ i, g i x = r i → g i v = 0) → v = 0 from H _ x0 hx0 hopt0 rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x hx hopt hN
  by_cases hv : ∀ v, (∀ i, g i x = r i → g i v = 0) → v = 0
  · exact ⟨x, hx, hopt, hv⟩
  push_neg at hv
  obtain ⟨v, hv1, hv2⟩ := hv
  obtain ⟨w, hw1, hw2, hw3⟩ : ∃ w, (∀ i, g i x = r i → g i w = 0) ∧ w ≠ 0 ∧ φ w ≤ 0 := by
    rcases le_total (φ v) 0 with h | h
    · exact ⟨v, hv1, hv2, h⟩
    · refine ⟨-v, fun i hi => by rw [map_neg, hv1 i hi, neg_zero], neg_ne_zero.mpr hv2, ?_⟩
      rw [map_neg]; linarith
  obtain ⟨s, hs, hns⟩ := hray x hx w hw2
  push_neg at hns
  obtain ⟨i0, hi0⟩ := hns
  simp only [map_add, map_smul, smul_eq_mul] at hi0
  have hgi0 : 0 < g i0 w := by
    have := hx i0
    by_contra hc; push_neg at hc
    nlinarith
  set A := Finset.univ.filter fun i => 0 < g i w with hA
  have hAne : A.Nonempty := ⟨i0, by simp [A, hgi0]⟩
  set f : ι → ℝ := fun i => (r i - g i x) / g i w with hf
  set s' := A.inf' hAne f with hs'
  obtain ⟨c, hcA, hc⟩ := Finset.exists_mem_eq_inf' hAne f
  have hcpos : 0 < g c w := (Finset.mem_filter.mp hcA).2
  have hs'0 : 0 ≤ s' := by
    apply Finset.le_inf'
    intro i hi
    exact div_nonneg (by linarith [hx i]) (Finset.mem_filter.mp hi).2.le
  set x' := x + s' • w
  have hgx' : ∀ i, g i x' = g i x + s' * g i w := by
    intro i; simp [x', map_add, map_smul, smul_eq_mul]
  have hx' : ∀ i, g i x' ≤ r i := by
    intro i
    rw [hgx']
    by_cases hi : 0 < g i w
    · have h1 : s' ≤ f i := Finset.inf'_le (s := A) f (by simp [A, hi])
      have h2 : s' * g i w ≤ r i - g i x := by
        have := (le_div_iff₀ hi).mp h1; linarith
      linarith
    · push_neg at hi
      have := mul_nonpos_of_nonneg_of_nonpos hs'0 hi
      linarith [hx i]
  have hopt' : ∀ x'', (∀ i, g i x'' ≤ r i) → φ x' ≤ φ x'' := by
    intro x'' hx''
    have : φ x' = φ x + s' * φ w := by simp [x', map_add, map_smul, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos hs'0 hw3
    linarith [hopt x'' hx'']
  have hsub : (Finset.univ.filter fun i => g i x' < r i) ⊂
      (Finset.univ.filter fun i => g i x < r i) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨c, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases lt_or_eq_of_le (hx c) with h | h
        · exact h
        · exact absurd (hw1 c h) hcpos.ne'
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        rw [hgx', show s' = f c from hc]
        simp only [f]
        rw [div_mul_cancel₀ _ hcpos.ne']
        linarith
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      rcases lt_or_eq_of_le (hx i) with h' | h'
      · exact h'
      · rw [hgx', hw1 i h', h'] at h; linarith
  exact ih _ (hN ▸ Finset.card_lt_card hsub) x' hx' hopt' rfl

theorem param_pl' {V : Type} [AddCommGroup V] [Module ℝ V] {ι : Type} [Fintype ι]
    (g : ι → V →ₗ[ℝ] ℝ) (r k : ι → ℝ) (φ : V →ₗ[ℝ] ℝ) (B L0 : ℝ) (C : ℝ → ℝ)
    (hray : ∀ lam x, (∀ i, g i x ≤ r i + k i * lam) → ∀ v, v ≠ 0 →
      ∃ s : ℝ, 0 < s ∧ ¬ ∀ i, g i (x + s • v) ≤ r i + k i * lam)
    (hC : ∀ lam, L0 ≤ lam → (∃ x, (∀ i, g i x ≤ r i + k i * lam) ∧ C lam = φ x + B) ∧
      ∀ x, (∀ i, g i x ≤ r i + k i * lam) → C lam ≤ φ x + B)
    (hconv : ConvexOn ℝ (Set.Ici L0) C) : IsPiecewiseLinearOn C (Set.Ici L0) := by
  classical
  let AT : (T : Finset ι) → (V →ₗ[ℝ] (T → ℝ)) := fun T => LinearMap.pi (fun c : T => g c.1)
  let u : Finset ι → V := fun T => (AT T).leftInverse (fun c => r c.1)
  let w : Finset ι → V := fun T => (AT T).leftInverse (fun c => k c.1)
  have hpath : ∀ T lam i, g i (u T + lam • w T) = g i (u T) + lam * g i (w T) := by
    intro T lam i; simp [map_add, map_smul, smul_eq_mul]
  have hφpath : ∀ T lam, φ (u T + lam • w T) = φ (u T) + lam * φ (w T) := by
    intro T lam; simp [map_add, map_smul, smul_eq_mul]
  apply assemble' L0 C (Finset ι) ι (fun T => φ (u T) + B) (fun T => φ (w T))
    (fun T i => g i (w T) - k i) (fun T i => g i (u T) - r i) _ _ hconv
  · intro lam hlam
    obtain ⟨⟨x0, hx0, hCx0⟩, hmin⟩ := hC lam hlam
    obtain ⟨x, hx, hopt, hvert⟩ := vertex_exists' g (fun i => r i + k i * lam) φ (hray lam)
      x0 hx0 (fun x' hx' => by have := hmin x' hx'; linarith)
    have hCx : C lam = φ x + B := by
      have h1 := hmin x hx
      have h2 := hopt x0 hx0
      linarith
    let T := Finset.univ.filter fun i => g i x = r i + k i * lam
    have hker : LinearMap.ker (AT T) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      apply hvert
      intro i hi
      have := congrFun hv ⟨i, by simp [T, hi]⟩
      simpa [AT] using this
    have hAx : AT T x = (fun c : T => r c.1) + lam • (fun c : T => k c.1) := by
      funext c
      have := (Finset.mem_filter.mp c.2).2
      simp [AT, this, mul_comm]
    have hxpath : x = u T + lam • w T := by
      have := LinearMap.leftInverse_apply_of_inj hker x
      rw [hAx, map_add, map_smul] at this
      exact this.symm
    refine ⟨T, fun i => ?_, ?_⟩
    · have := hx i
      rw [hxpath, hpath] at this
      linarith
    · rw [hCx, hxpath, hφpath]; ring
  · intro T lam hlam hcond
    have hfeas : ∀ i, g i (u T + lam • w T) ≤ r i + k i * lam := by
      intro i; rw [hpath]; have := hcond i; linarith
    have := (hC lam hlam).2 _ hfeas
    rw [hφpath] at this
    linarith


section Concrete
variable {n : ℕ}

abbrev VV (n : ℕ) := (Fin (n + 1) → Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)

def ycoord (i j : Fin (n + 1)) : VV n →ₗ[ℝ] ℝ where
  toFun x := x.1 i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tcoord (j : Fin (n + 1)) : VV n →ₗ[ℝ] ℝ where
  toFun x := x.2 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ycoord_apply (i j : Fin (n + 1)) (x : VV n) : ycoord i j x = x.1 i j := rfl
@[simp] lemma tcoord_apply (j : Fin (n + 1)) (x : VV n) : tcoord j x = x.2 j := rfl

abbrev CI (n : ℕ) := ((Fin (n + 1) × Fin (n + 1)) × Fin 3) ⊕ Fin 4

noncomputable def gC (N : ProjectNetwork n) : CI n → VV n →ₗ[ℝ] ℝ
  | Sum.inl (e, j) =>
    if j = 0 then (if e ∈ N.P then -ycoord e.1 e.2 else ycoord e.1 e.2)
    else if j = 1 then (if e ∈ N.P then ycoord e.1 e.2 else -ycoord e.1 e.2)
    else (if e ∈ N.P then ycoord e.1 e.2 - tcoord e.2 + tcoord e.1 else 0)
  | Sum.inr j =>
    if j = 0 then tcoord 0 else if j = 1 then -tcoord 0
    else if j = 2 then tcoord (Fin.last n) else -tcoord (Fin.last n)

noncomputable def rC {N : ProjectNetwork n} (J : JobData N) : CI n → ℝ
  | Sum.inl (e, j) =>
    if j = 0 then (if e ∈ N.P then -J.d e.1 e.2 else 0)
    else if j = 1 then (if e ∈ N.P then J.D e.1 e.2 else 0) else 0
  | Sum.inr _ => 0

noncomputable def kC : CI n → ℝ
  | Sum.inl _ => 0
  | Sum.inr j => if j = 2 then 1 else if j = 3 then -1 else 0

lemma feas_sched' {N : ProjectNetwork n} (J : JobData N) (lam : ℝ) (x : VV n)
    (h : ∀ i, gC N i x ≤ rC J i + kC i * lam) :
    IsSchedule J lam x.1 x.2 ∧ ∀ i j, (i, j) ∉ N.P → x.1 i j = 0 := by
  refine ⟨⟨fun e he => ⟨?_, ?_⟩, fun e he => ?_, ?_, ?_⟩, fun i j hij => ?_⟩
  · have := h (Sum.inl (e, 0)); simp [gC, rC, kC, he] at this; linarith
  · have := h (Sum.inl (e, 1)); simp [gC, rC, kC, he] at this; linarith
  · have := h (Sum.inl (e, 2)); simp [gC, rC, kC, he] at this; linarith
  · have h1 := h (Sum.inr 0); have h2 := h (Sum.inr 1)
    simp [gC, rC, kC] at h1 h2; linarith
  · have h1 := h (Sum.inr 2); have h2 := h (Sum.inr 3)
    simp [gC, rC, kC] at h1 h2; linarith
  · have h1 := h (Sum.inl ((i, j), 0)); have h2 := h (Sum.inl ((i, j), 1))
    simp [gC, rC, kC, hij] at h1 h2; linarith

lemma sched_feas' {N : ProjectNetwork n} (J : JobData N) (lam : ℝ) (y t)
    (h : IsSchedule J lam y t) : ∀ i, gC N i (trunc' N y, t) ≤ rC J i + kC i * lam := by
  intro i
  rcases i with ⟨e, j⟩ | j
  · by_cases he : e ∈ N.P
    · have h1 := h.1 e he; have h2 := h.2.1 e he
      fin_cases j <;> simp [gC, rC, kC, he, trunc'] <;> linarith
    · fin_cases j <;> simp [gC, rC, kC, he, trunc']
  · have h1 := h.2.2.1; have h2 := h.2.2.2
    fin_cases j <;> simp [gC, rC, kC, h1, h2]

noncomputable def φC {N : ProjectNetwork n} (J : JobData N) : VV n →ₗ[ℝ] ℝ :=
  ∑ e ∈ N.P, J.a e.1 e.2 • ycoord e.1 e.2

lemma cost_φ' {N : ProjectNetwork n} (J : JobData N) (x : VV n) :
    projectCost J x.1 = φC J x + ∑ e ∈ N.P, J.b e.1 e.2 := by
  simp [projectCost, φC, Finset.sum_add_distrib, LinearMap.sum_apply]

lemma ray_zero' (a b lo hi : ℝ) (h : ∀ s : ℝ, 0 < s → lo ≤ a + s * b ∧ a + s * b ≤ hi) : b = 0 := by
  by_contra hb
  have h1 := h 1 one_pos
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hs : 0 < (hi - lo + 1) / (-b) + 1 := by
      have : 0 ≤ (hi - lo + 1) / (-b) := div_nonneg (by linarith) (by linarith)
      linarith
    have h2 := h _ hs
    have : ((hi - lo + 1) / (-b)) * b = -(hi - lo + 1) := by field_simp
    nlinarith
  · have hs : 0 < (hi - lo + 1) / b + 1 := by
      have : 0 ≤ (hi - lo + 1) / b := div_nonneg (by linarith) (by linarith)
      linarith
    have h2 := h _ hs
    have : ((hi - lo + 1) / b) * b = (hi - lo + 1) := by field_simp
    nlinarith

lemma goal_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (C : ℝ → ℝ)
    (hC : ∀ lam ∈ feasibleDurations J, IsLeast (costSet J lam) (C lam)) :
    AntitoneOn C (feasibleDurations J) ∧
      IsPiecewiseLinearOn C (feasibleDurations J) ∧
      ConvexOn ℝ (feasibleDurations J) C := by
  have hanti : AntitoneOn C (feasibleDurations J) := by
    intro l1 h1 l2 h2 hle
    obtain ⟨y, t, hs, hc⟩ := (hC l1 h1).1
    rw [hc]
    apply (hC l2 h2).2
    refine ⟨y, fun j => if j = Fin.last n then l2 else t j, ⟨hs.1, fun e he => ?_, ?_, by simp⟩, rfl⟩
    · have hlt := N.label_lt e he
      have h1' : e.1 ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last _))
      have h2' := hs.2.1 e he
      simp only [h1', if_false]
      split_ifs with h3
      · have := hs.2.2.2; rw [h3] at h2' ⊢; linarith
      · exact h2'
    · simp [Ne.symm (last_ne_zero' N), hs.2.2.1]
  have hconv : ConvexOn ℝ (feasibleDurations J) C := by
    refine ⟨?_, ?_⟩
    · rw [feasible_core]; exact convex_Ici _
    intro l1 h1 l2 h2 a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    obtain ⟨y1, t1, hs1, hc1⟩ := (hC l1 h1).1
    obtain ⟨y2, t2, hs2, hc2⟩ := (hC l2 h2).1
    have hmix : a • l1 + (1 - a) • l2 ∈ feasibleDurations J := by
      rw [feasible_core] at h1 h2 ⊢
      simp only [Set.mem_Ici, smul_eq_mul] at h1 h2 ⊢
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    have := (hC _ hmix).2 ⟨fun i j => a * y1 i j + (1 - a) * y2 i j, fun j => a * t1 j + (1 - a) * t2 j,
      ⟨fun e he => ⟨?_, ?_⟩, fun e he => ?_, ?_, ?_⟩, rfl⟩
    · refine le_trans this (le_of_eq ?_)
      rw [hc1, hc2]
      simp only [projectCost, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    · have h1 := (hs1.1 e he).1; have h2 := (hs2.1 e he).1
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    · have h1 := (hs1.1 e he).2; have h2 := (hs2.1 e he).2
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    · have h1 := hs1.2.1 e he; have h2 := hs2.2.1 e he
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    · simp [hs1.2.2.1, hs2.2.2.1]
    · simp [hs1.2.2.2, hs2.2.2.2, smul_eq_mul]
  refine ⟨hanti, ?_, hconv⟩
  have hS := feasible_core N J
  rw [hS] at hconv ⊢
  apply param_pl' (gC N) (rC J) kC (φC J) (∑ e ∈ N.P, J.b e.1 e.2) _ C ?_ ?_ hconv
  · intro lam x hx v hv
    by_contra hcon
    push_neg at hcon
    apply hv
    have hF : ∀ s : ℝ, 0 < s → IsSchedule J lam (x + s • v).1 (x + s • v).2 ∧
        ∀ i j, (i, j) ∉ N.P → (x + s • v).1 i j = 0 := fun s hs =>
      feas_sched' J lam _ (hcon s hs)
    obtain ⟨vy, vt⟩ := v
    obtain ⟨xy, xt⟩ := x
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hF
    ext i j
    · show vy i j = 0
      by_cases he : (i, j) ∈ N.P
      · apply ray_zero' (xy i j) (vy i j) (J.d i j) (J.D i j)
        intro s hs
        have := ((hF s hs).1.1 (i, j) he)
        simpa using this
      · apply ray_zero' (xy i j) (vy i j) 0 0
        intro s hs
        have := (hF s hs).2 i j he
        simp at this
        constructor <;> linarith
    · show vt i = 0
      apply ray_zero' (xt i) (vt i) 0 lam
      intro s hs
      have := sched_bounds' J (hF s hs).1 i
      simpa using this
  · intro lam hlam
    have hmem : lam ∈ feasibleDurations J := by rw [hS]; exact hlam
    obtain ⟨⟨y0, t0, hs0, hc0⟩, hlow⟩ := hC lam hmem
    refine ⟨⟨(trunc' N y0, t0), sched_feas' J lam y0 t0 hs0, ?_⟩, fun x hx => ?_⟩
    · rw [hc0, ← trunc_cost' J y0, cost_φ' J (trunc' N y0, t0)]
    · have := hlow ⟨x.1, x.2, (feas_sched' J lam x hx).1, rfl⟩
      rw [cost_φ'] at this
      exact this

end Concrete

end CriticalPath.CostCurve

open CriticalPath.CostCurve


theorem solution {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (C : ℝ → ℝ)
    (hC : ∀ lam ∈ feasibleDurations J, IsLeast (costSet J lam) (C lam)) :
    AntitoneOn C (feasibleDurations J) ∧
      IsPiecewiseLinearOn C (feasibleDurations J) ∧
      ConvexOn ℝ (feasibleDurations J) C := by
  exact goal_core N J C hC
