-- Prove2me | solution 1 for AvgCompletionSched.BestAlpha.random_alpha_exp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:56:01.543991+00:00
-- url     : https://prove2.me/submissions/56e8f9e7-590c-40fc-aff9-f3207f369da4

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

set_option autoImplicit false

namespace RAE_e5ddc447

open MeasureTheory AvgCompletionSched.BestAlpha

variable {n : ℕ} {I : Instance n}

noncomputable def idleV (P : PreemptiveSchedule I) (t : ℝ) : ℝ :=
  (volume ({s | P.σ s = none} ∩ Set.Ico 0 t)).toReal

lemma vol_ne_top (A : Set ℝ) (t : ℝ) : volume (A ∩ Set.Ico 0 t) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_Ico_lt_top (a := (0:ℝ)) (b := t)).ne
    (measure_mono Set.inter_subset_right)

lemma done_mono (P : PreemptiveSchedule I) (j : Fin n) {t t' : ℝ} (h : t ≤ t') :
    P.done j t ≤ P.done j t' :=
  ENNReal.toReal_mono (vol_ne_top _ _)
    (measure_mono (Set.inter_subset_inter_right _ (Set.Ico_subset_Ico_right h)))

lemma done_lip (P : PreemptiveSchedule I) (j : Fin n) {t t' : ℝ} (h : t ≤ t') :
    P.done j t' ≤ P.done j t + (t' - t) := by
  unfold PreemptiveSchedule.done
  have hsub : {s | P.σ s = some j} ∩ Set.Ico 0 t' ⊆
      ({s | P.σ s = some j} ∩ Set.Ico 0 t) ∪ Set.Ico t t' := by
    rintro s ⟨hs1, hs2, hs3⟩
    by_cases hst : s < t
    · exact Or.inl ⟨hs1, hs2, hst⟩
    · exact Or.inr ⟨not_lt.mp hst, hs3⟩
  have h1 := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [Real.volume_Ico] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨vol_ne_top _ _, ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add (vol_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at h2
  exact h2

lemma done_le_p (P : PreemptiveSchedule I) (j : Fin n) (t : ℝ) : P.done j t ≤ I.p j := by
  unfold PreemptiveSchedule.done
  have := ENNReal.toReal_mono (by rw [P.total j]; exact ENNReal.ofReal_ne_top)
    (measure_mono (μ := volume) (Set.inter_subset_left (s := {s | P.σ s = some j})
      (t := Set.Ico 0 t)))
  rwa [P.total j, ENNReal.toReal_ofReal (I.p_pos j).le] at this

lemma done_nonneg (P : PreemptiveSchedule I) (j : Fin n) (t : ℝ) : 0 ≤ P.done j t :=
  ENNReal.toReal_nonneg

lemma done_zero (P : PreemptiveSchedule I) (j : Fin n) (t : ℝ) (ht : t ≤ I.r j) :
    P.done j t = 0 := by
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Set.Ico 0 t = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]
    intro h _
    exact le_trans ht (P.released s j h)
  rw [this]; simp

lemma done_full (P : PreemptiveSchedule I) (j : Fin n) :
    ∃ T, ∀ t, T ≤ t → P.done j t = I.p j := by
  obtain ⟨T0, hT0⟩ := P.bounded j
  refine ⟨T0, fun t ht => ?_⟩
  unfold PreemptiveSchedule.done
  have : {s | P.σ s = some j} ∩ Set.Ico 0 t = {s | P.σ s = some j} := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, and_iff_left_iff_imp]
    intro h
    exact ⟨P.nonneg s j h, lt_of_lt_of_le (hT0 s h) ht⟩
  rw [this, P.total j, ENNReal.toReal_ofReal (I.p_pos j).le]

lemma bdd (P : PreemptiveSchedule I) (j : Fin n) (c : ℝ) (hc : 0 < c) :
    BddBelow {t | c ≤ P.done j t} := by
  refine ⟨I.r j, fun t ht => ?_⟩
  by_contra h
  push_neg at h
  have := done_zero P j t h.le
  simp only [Set.mem_setOf_eq] at ht
  linarith

lemma nonempty (P : PreemptiveSchedule I) (j : Fin n) (c : ℝ) (hc : c ≤ I.p j) :
    {t | c ≤ P.done j t}.Nonempty := by
  obtain ⟨T, hT⟩ := done_full P j
  exact ⟨T, by simp only [Set.mem_setOf_eq]; rw [hT T le_rfl]; exact hc⟩

lemma CPα_mem (P : PreemptiveSchedule I) (j : Fin n) (α : ℝ) (h0 : 0 < α) (h1 : α ≤ 1) :
    α * I.p j ≤ P.done j (P.CPα j α) := by
  have hp := I.p_pos j
  have hc : 0 < α * I.p j := mul_pos h0 hp
  have hcp : α * I.p j ≤ I.p j := by nlinarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt (nonempty P j _ hcp)
    (lt_add_of_pos_right (P.CPα j α) hε)
  have hCs : P.CPα j α ≤ s := csInf_le (bdd P j _ hc) hs
  have := done_lip P j hCs
  simp only [Set.mem_setOf_eq] at hs
  linarith

lemma r_lt_CPα (P : PreemptiveSchedule I) (j : Fin n) (α : ℝ) (h0 : 0 < α) (h1 : α ≤ 1) :
    I.r j < P.CPα j α := by
  by_contra h
  push_neg at h
  have h2 := CPα_mem P j α h0 h1
  rw [done_zero P j _ h] at h2
  have := mul_pos h0 (I.p_pos j)
  linarith

lemma done_le_of_le (P : PreemptiveSchedule I) (j : Fin n) (α : ℝ) (h0 : 0 < α)
    (t : ℝ) (ht : t ≤ P.CPα j α) : P.done j t ≤ α * I.p j := by
  have hc : 0 < α * I.p j := mul_pos h0 (I.p_pos j)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hlt : t - ε < P.CPα j α := by linarith
  have hnm := notMem_of_lt_csInf hlt (bdd P j _ hc)
  simp only [Set.mem_setOf_eq, not_le] at hnm
  have := done_lip P j (show t - ε ≤ t by linarith)
  linarith

lemma CPα_mono (P : PreemptiveSchedule I) (j : Fin n) {α β : ℝ} (h0 : 0 < α) (hab : α ≤ β)
    (hb : β ≤ 1) : P.CPα j α ≤ P.CPα j β := by
  have hp := I.p_pos j
  apply csInf_le_csInf (bdd P j _ (mul_pos h0 hp)) (nonempty P j _ (by nlinarith))
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  nlinarith

lemma CP_eq (P : PreemptiveSchedule I) (j : Fin n) : P.CP j = P.CPα j 1 := by
  simp [PreemptiveSchedule.CP, PreemptiveSchedule.CPα]

lemma decomp (P : PreemptiveSchedule I) (t : ℝ) (ht : 0 ≤ t) :
    t = idleV P t + ∑ k, P.done k t := by
  have hm : ∀ o : Option (Fin n), MeasurableSet {s | P.σ s = o} := by
    intro o
    cases o with
    | some j => exact P.measurableSet_run j
    | none =>
      have : {s | P.σ s = none} = (⋃ j, {s | P.σ s = some j})ᶜ := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        cases P.σ s <;> simp
      rw [this]
      exact (MeasurableSet.iUnion fun j => P.measurableSet_run j).compl
  have hU : Set.Ico (0:ℝ) t = ⋃ o : Option (Fin n), ({s | P.σ s = o} ∩ Set.Ico 0 t) := by
    ext s; simp
  have hd : Pairwise (Function.onFun Disjoint
      fun o : Option (Fin n) => {s | P.σ s = o} ∩ Set.Ico 0 t) := by
    intro a b hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro s ⟨h1, -⟩ ⟨h2, -⟩
    exact hab (h1.symm.trans h2)
  have hmu := measure_iUnion (μ := volume) hd (fun o => (hm o).inter measurableSet_Ico)
  rw [← hU, tsum_fintype, Fintype.sum_option, Real.volume_Ico, sub_zero] at hmu
  have := congrArg ENNReal.toReal hmu
  rw [ENNReal.toReal_ofReal ht, ENNReal.toReal_add (vol_ne_top _ _)
    (ENNReal.sum_ne_top.2 fun k _ => vol_ne_top _ _),
    ENNReal.toReal_sum (fun k _ => vol_ne_top _ _)] at this
  simp only [idleV, PreemptiveSchedule.done]
  exact this

lemma idleV_mono (P : PreemptiveSchedule I) {t t' : ℝ} (h : t ≤ t') : idleV P t ≤ idleV P t' :=
  ENNReal.toReal_mono (vol_ne_top _ _)
    (measure_mono (Set.inter_subset_inter_right _ (Set.Ico_subset_Ico_right h)))

/-! list scheduling -/

noncomputable def pp (I : Instance n) (π : Fin n ≃ Fin n) (m : ℕ) : ℝ :=
  if h : m < n then I.p (π ⟨m, h⟩) else 0

lemma list_bound (π : Fin n ≃ Fin n) : ∀ k, k ≤ n → ∀ c : ℝ,
    (∀ l (hl : l < n), l < k → I.r (π ⟨l, hl⟩) + ∑ m ∈ Finset.Ico l k, pp I π m ≤ c) →
    ∑ m ∈ Finset.range k, pp I π m ≤ c → listFinish I π k ≤ c := by
  intro k
  induction k with
  | zero => intro _ c _ h; simpa [listFinish] using h
  | succ k ih =>
    intro hk c h1 h2
    have hkn : k < n := by omega
    have hpk : pp I π k = I.p (π ⟨k, hkn⟩) := by simp [pp, hkn]
    rw [listFinish, dif_pos hkn]
    have hA : I.r (π ⟨k, hkn⟩) ≤ c - I.p (π ⟨k, hkn⟩) := by
      have := h1 k hkn (by omega)
      rw [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add, hpk] at this
      linarith
    have hB : listFinish I π k ≤ c - I.p (π ⟨k, hkn⟩) := by
      have := ih (by omega) (c - I.p (π ⟨k, hkn⟩))
        (fun l hl hlk => by
          have := h1 l hl (by omega)
          rw [Finset.sum_Ico_succ_top hlk.le, hpk] at this
          linarith)
        (by rw [Finset.sum_range_succ, hpk] at h2; linarith)
      linarith
    have := max_le hA hB
    linarith

lemma sum_conv (π : Fin n ≃ Fin n) (a b : ℕ) (hb : b ≤ n) :
    ∑ m ∈ Finset.Ico a b, pp I π m =
      ∑ m : Fin n, if a ≤ (m : ℕ) ∧ (m : ℕ) < b then I.p (π m) else 0 := by
  have : ∀ m : Fin n, (if a ≤ (m : ℕ) ∧ (m : ℕ) < b then I.p (π m) else 0) =
      (fun m : ℕ => if a ≤ m ∧ m < b then pp I π m else 0) m := by
    intro m
    simp [pp, m.2]
  rw [Finset.sum_congr rfl (fun m _ => this m)]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if a ≤ m ∧ m < b then pp I π m else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

lemma listFinish_nonneg (π : Fin n ≃ Fin n) : ∀ k, 0 ≤ listFinish I π k := by
  intro k
  induction k with
  | zero => simp [listFinish]
  | succ k ih =>
    rw [listFinish]
    split_ifs with h
    · have := I.p_pos (π ⟨k, h⟩)
      have := le_max_right (I.r (π ⟨k, h⟩)) (listFinish I π k)
      linarith
    · exact ih

noncomputable def Hf (α x : ℝ) : ℝ := if α ≤ x then 1 + α else x

lemma Calpha_le (P : PreemptiveSchedule I) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (j : Fin n) :
    P.Calpha α j ≤ P.idle j + ∑ k, Hf α (P.frac j k) * I.p k := by
  unfold PreemptiveSchedule.Calpha listCompletion
  set π := alphaOrder P α with hπ
  have hmono : Monotone ((fun k => toLex (P.CPα k α, k)) ∘ π) := Tuple.monotone_sort _
  have hord : ∀ a b : Fin n, a ≤ b → P.CPα (π a) α ≤ P.CPα (π b) α := by
    intro a b hab
    have := hmono hab
    simp only [Function.comp_apply] at this
    rcases Prod.Lex.toLex_le_toLex.1 this with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  set q := π.symm j with hq
  have hqj : π q = j := π.apply_symm_apply j
  have hjC : P.CPα j α ≤ P.CP j := by
    rw [CP_eq]; exact CPα_mono P j hα0 hα1 le_rfl
  have key : ∀ l (hl : l < n), l < (q : ℕ) + 1 →
      I.r (π ⟨l, hl⟩) + ∑ m ∈ Finset.Ico l ((q : ℕ) + 1), pp I π m ≤
        P.idle j + ∑ k, Hf α (P.frac j k) * I.p k := by
    intro l hl hlq
    rw [sum_conv π l ((q : ℕ) + 1) (by omega)]
    rw [← Equiv.sum_comp π.symm]
    simp only [Equiv.apply_symm_apply]
    set lm : Fin n := ⟨l, hl⟩
    set t := P.CPα (π lm) α with ht
    have hti : I.r (π lm) ≤ t := (r_lt_CPα P _ α hα0 hα1).le
    have ht0 : 0 ≤ t := le_trans (I.r_nonneg _) hti
    have htj : t ≤ P.CPα j α := by
      have := hord lm q (by rw [Fin.le_def]; simp [lm]; omega)
      rwa [hqj] at this
    have htC : t ≤ P.CP j := htj.trans hjC
    have hdec := decomp P t ht0
    have hidle : idleV P t ≤ P.idle j := idleV_mono P htC
    have perk : ∀ k : Fin n, P.done k t +
        (if l ≤ ((π.symm k : Fin n) : ℕ) ∧ ((π.symm k : Fin n) : ℕ) < (q : ℕ) + 1
          then I.p k else 0) ≤ Hf α (P.frac j k) * I.p k := by
      intro k
      have hp := I.p_pos k
      have hX : P.frac j k * I.p k = P.done k (P.CP j) := by
        unfold PreemptiveSchedule.frac; field_simp
      have hD1 := done_le_p P k t
      have hD2 : P.done k t ≤ P.done k (P.CP j) := done_mono P k htC
      have F1 : ((π.symm k : Fin n) : ℕ) ≤ (q : ℕ) → α ≤ P.frac j k := by
        intro h
        have h' : P.CPα k α ≤ P.CPα j α := by
          have := hord (π.symm k) q (by rw [Fin.le_def]; exact h)
          rwa [Equiv.apply_symm_apply, hqj] at this
        have h1 := CPα_mem P k α hα0 hα1
        have h2 := done_mono P k (h'.trans hjC)
        unfold PreemptiveSchedule.frac
        rw [le_div_iff₀ hp]
        linarith
      have F2 : l ≤ ((π.symm k : Fin n) : ℕ) → P.done k t ≤ α * I.p k := by
        intro h
        have h' : t ≤ P.CPα k α := by
          have := hord lm (π.symm k) (by rw [Fin.le_def]; exact h)
          rwa [Equiv.apply_symm_apply] at this
        exact done_le_of_le P k α hα0 t h'
      have hap : 0 < α * I.p k := mul_pos hα0 hp
      have e1 : (1 + α) * I.p k = I.p k + α * I.p k := by ring
      by_cases hqk : ((π.symm k : Fin n) : ℕ) < (q : ℕ) + 1
      · have hx := F1 (by omega)
        unfold Hf
        rw [if_pos hx]
        by_cases hl' : l ≤ ((π.symm k : Fin n) : ℕ)
        · rw [if_pos ⟨hl', hqk⟩]
          have := F2 hl'
          linarith
        · rw [if_neg (fun h => hl' h.1)]
          linarith
      · rw [if_neg (fun h => hqk h.2)]
        have hD3 := F2 (by omega)
        unfold Hf
        by_cases hx : α ≤ P.frac j k
        · rw [if_pos hx]; linarith
        · rw [if_neg hx]; linarith
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => perk k)
    rw [Finset.sum_add_distrib] at hsum
    have : P.idle j = idleV P (P.CP j) := rfl
    linarith
  refine list_bound π ((q : ℕ) + 1) (by omega) _ key ?_
  have h0 := key 0 (by omega) (by omega)
  rw [← Finset.range_eq_Ico] at h0
  have := I.r_nonneg (π ⟨0, by omega⟩)
  linarith

/-! measurability of α ↦ Calpha -/

lemma meas_sortset (π : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | Tuple.sort (fun k => toLex (x k, k)) = π} := by
  have hset : ∀ a b : Fin n, MeasurableSet {x : Fin n → ℝ | a ≤ b →
      (x (π a) < x (π b) ∨ x (π a) = x (π b) ∧ π a ≤ π b)} := by
    intro a b
    by_cases hab : a ≤ b
    · simp only [hab, true_implies, Set.setOf_or, Set.setOf_and]
      exact (measurableSet_lt (measurable_pi_apply (π a)) (measurable_pi_apply (π b))).union
        ((measurableSet_eq_fun (measurable_pi_apply (π a)) (measurable_pi_apply (π b))).inter
          (MeasurableSet.const _))
    · simp [hab]
  have heq : {x : Fin n → ℝ | Tuple.sort (fun k => toLex (x k, k)) = π} =
      ⋂ a, ⋂ b, {x : Fin n → ℝ | a ≤ b →
        (x (π a) < x (π b) ∨ x (π a) = x (π b) ∧ π a ≤ π b)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h a b hab
      have := Tuple.monotone_sort (fun k => toLex (x k, k)) hab
      rw [h] at this
      simp only [Function.comp_apply] at this
      exact Prod.Lex.toLex_le_toLex.1 this
    · intro h
      symm
      rw [Tuple.eq_sort_iff]
      refine ⟨fun a b hab => ?_, fun a b hab heq => ?_⟩
      · simp only [Function.comp_apply]
        exact Prod.Lex.toLex_le_toLex.2 (h a b hab)
      · exfalso
        have := congrArg (fun z => (ofLex z).2) heq
        simp only [ofLex_toLex] at this
        exact hab.ne (π.injective this)
  rw [heq]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => hset a b

lemma meas_F (j : Fin n) :
    Measurable (fun x : Fin n → ℝ => listCompletion I (Tuple.sort (fun k => toLex (x k, k))) j) := by
  classical
  have : (fun x : Fin n → ℝ => listCompletion I (Tuple.sort (fun k => toLex (x k, k))) j) =
      fun x => ∑ π : Equiv.Perm (Fin n),
        if Tuple.sort (fun k => toLex (x k, k)) = π then listCompletion I π j else 0 := by
    funext x
    rw [Finset.sum_ite_eq]
    simp
  rw [this]
  exact Finset.measurable_sum _ (fun π _ =>
    Measurable.ite (meas_sortset π) measurable_const measurable_const)

lemma aemeas_Calpha (P : PreemptiveSchedule I) (j : Fin n) :
    AEMeasurable (fun α => P.Calpha α j) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  have hv : AEMeasurable (fun α => fun k => P.CPα k α) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine aemeasurable_pi_lambda _ fun k => ?_
    refine aemeasurable_restrict_of_monotoneOn measurableSet_Ioc ?_
    intro a ha b hb hab
    exact CPα_mono P k ha.1 hab hb.2
  exact (meas_F (I := I) j).comp_aemeasurable hv

/-! integrals -/

lemma ii_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun a => ∑ i ∈ s, f i a) volume 0 1 :=
  ⟨integrable_finsetSum s fun i hi => (h i hi).1, integrable_finsetSum s fun i hi => (h i hi).2⟩

lemma integral_H (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IntervalIntegrable (fun α => Real.exp α * Hf α x) volume 0 1 ∧
    ∫ α in (0:ℝ)..1, Real.exp α * Hf α x = x * Real.exp 1 := by
  have h1 : IntervalIntegrable (fun α => Real.exp α * Hf α x) volume 0 x := by
    have hc : IntervalIntegrable (fun α => Real.exp α * (1 + α)) volume 0 x :=
      (by fun_prop : Continuous fun α : ℝ => Real.exp α * (1 + α)).intervalIntegrable _ _
    refine hc.congr_ae ?_
    rw [Set.uIoc_of_le hx0]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun α hα => ?_
    simp [Hf, hα.2]
  have h2 : IntervalIntegrable (fun α => Real.exp α * Hf α x) volume x 1 := by
    have hc : IntervalIntegrable (fun α => Real.exp α * x) volume x 1 :=
      (by fun_prop : Continuous fun α : ℝ => Real.exp α * x).intervalIntegrable _ _
    refine hc.congr_ae ?_
    rw [Set.uIoc_of_le hx1]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun α hα => ?_
    simp [Hf, not_le.mpr hα.1]
  refine ⟨h1.trans h2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ α in (0:ℝ)..x, Real.exp α * Hf α x = ∫ α in (0:ℝ)..x, Real.exp α * (1 + α) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun α hα => ?_)
    rw [Set.uIoc_of_le hx0] at hα
    simp [Hf, hα.2]
  have e2 : ∫ α in x..1, Real.exp α * Hf α x = ∫ α in x..1, Real.exp α * x := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun α hα => ?_)
    rw [Set.uIoc_of_le hx1] at hα
    simp [Hf, not_le.mpr hα.1]
  have e3 : ∫ α in (0:ℝ)..x, Real.exp α * (1 + α) = x * Real.exp x - 0 * Real.exp 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun α => α * Real.exp α)
    · intro α _
      have h : HasDerivAt (fun y => y * Real.exp y) (1 * Real.exp α + α * Real.exp α) α :=
        (hasDerivAt_id' α).mul (Real.hasDerivAt_exp α)
      show HasDerivAt (fun α => α * Real.exp α) (Real.exp α * (1 + α)) α
      rw [show Real.exp α * (1 + α) = 1 * Real.exp α + α * Real.exp α by ring]
      exact h
    · exact (by fun_prop : Continuous fun α : ℝ => Real.exp α * (1 + α)).intervalIntegrable _ _
  rw [e1, e2, intervalIntegral.integral_mul_const, integral_exp, e3]
  ring

/-! nonpreemptive → preemptive -/

noncomputable def σN (N : NonpreemptiveSchedule I) (t : ℝ) : Option (Fin n) :=
  if h : ∃ j, N.S j ≤ t ∧ t < N.S j + I.p j then some h.choose else none

lemma σN_eq (N : NonpreemptiveSchedule I) (t : ℝ) (j : Fin n) :
    σN N t = some j ↔ N.S j ≤ t ∧ t < N.S j + I.p j := by
  unfold σN
  constructor
  · intro h
    split_ifs at h with hex
    · obtain rfl := Option.some_inj.mp h
      exact hex.choose_spec
  · intro hj
    have hex : ∃ j, N.S j ≤ t ∧ t < N.S j + I.p j := ⟨j, hj⟩
    rw [dif_pos hex]
    congr 1
    by_contra hne
    have hk := hex.choose_spec
    rcases N.noOverlap _ _ hne with h1 | h1
    · linarith [hk.1, hk.2, hj.1, hj.2]
    · linarith [hk.1, hk.2, hj.1, hj.2]

lemma σN_set (N : NonpreemptiveSchedule I) (j : Fin n) :
    {s | σN N s = some j} = Set.Ico (N.S j) (N.S j + I.p j) := by
  ext s; simp [σN_eq, Set.mem_Ico]

noncomputable def ofNP (N : NonpreemptiveSchedule I) : PreemptiveSchedule I where
  σ := σN N
  measurableSet_run j := by rw [σN_set]; exact measurableSet_Ico
  nonneg t j h := le_trans (I.r_nonneg j) (le_trans (N.released j) ((σN_eq N t j).1 h).1)
  released t j h := le_trans (N.released j) ((σN_eq N t j).1 h).1
  total j := by rw [σN_set, Real.volume_Ico]; congr 1; ring
  bounded j := ⟨N.S j + I.p j, fun s hs => ((σN_eq N s j).1 hs).2⟩

lemma ofNP_CP (N : NonpreemptiveSchedule I) (j : Fin n) : (ofNP N).CP j ≤ N.C j := by
  have hp := I.p_pos j
  unfold PreemptiveSchedule.CP
  refine csInf_le (bdd (ofNP N) j _ hp) ?_
  simp only [Set.mem_setOf_eq, PreemptiveSchedule.done]
  have hS : 0 ≤ N.S j := le_trans (I.r_nonneg j) (N.released j)
  have : {s | (ofNP N).σ s = some j} ∩ Set.Ico 0 (N.C j) = Set.Ico (N.S j) (N.S j + I.p j) := by
    rw [show (ofNP N).σ = σN N from rfl, σN_set]
    unfold NonpreemptiveSchedule.C
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, le_trans hS h1, h2⟩
  rw [this, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  linarith

/-! per job integral bound -/

lemma frac_mem (P : PreemptiveSchedule I) (j k : Fin n) : 0 ≤ P.frac j k ∧ P.frac j k ≤ 1 := by
  have hp := I.p_pos k
  unfold PreemptiveSchedule.frac
  refine ⟨div_nonneg (done_nonneg P k _) hp.le, ?_⟩
  rw [div_le_one hp]
  exact done_le_p P k _

lemma CP_decomp (P : PreemptiveSchedule I) (j : Fin n) :
    P.CP j = P.idle j + ∑ k, P.frac j k * I.p k := by
  have h0 : 0 ≤ P.CP j := by
    rw [CP_eq]
    exact le_trans (I.r_nonneg j) (r_lt_CPα P j 1 one_pos le_rfl).le
  have := decomp P (P.CP j) h0
  have e : ∀ k, P.frac j k * I.p k = P.done k (P.CP j) := by
    intro k
    have hp := I.p_pos k
    unfold PreemptiveSchedule.frac; field_simp
  simp only [e]
  exact this

lemma job_bound (P : PreemptiveSchedule I) (j : Fin n) :
    IntervalIntegrable (fun α => Real.exp α / (Real.exp 1 - 1) * P.Calpha α j) volume 0 1 ∧
    ∫ α in (0:ℝ)..1, Real.exp α / (Real.exp 1 - 1) * P.Calpha α j
      ≤ Real.exp 1 / (Real.exp 1 - 1) * P.CP j := by
  have hE : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hE1 : 0 < Real.exp 1 - 1 := by linarith
  set f : ℝ → ℝ := fun α => Real.exp α / (Real.exp 1 - 1) with hf
  have hfpos : ∀ α, 0 < f α := fun α => div_pos (Real.exp_pos α) hE1
  have hfc : Continuous f := by fun_prop
  -- integrability of f * H
  have hH : ∀ k, IntervalIntegrable (fun α => f α * Hf α (P.frac j k)) volume 0 1 ∧
      ∫ α in (0:ℝ)..1, f α * Hf α (P.frac j k) =
        P.frac j k * (Real.exp 1 / (Real.exp 1 - 1)) := by
    intro k
    obtain ⟨hk0, hk1⟩ := frac_mem P j k
    obtain ⟨hi, hv⟩ := integral_H (P.frac j k) hk0 hk1
    have hfe : (fun α => f α * Hf α (P.frac j k)) =
        fun α => Real.exp α * Hf α (P.frac j k) / (Real.exp 1 - 1) := by
      funext α; simp only [hf]; ring
    rw [hfe]
    refine ⟨hi.div_const _, ?_⟩
    rw [intervalIntegral.integral_div, hv]
    ring
  set g : ℝ → ℝ := fun α => f α * P.idle j + ∑ k, I.p k * (f α * Hf α (P.frac j k)) with hg
  have h1 : IntervalIntegrable (fun α => f α * P.idle j) volume 0 1 :=
    (hfc.mul continuous_const).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun α => ∑ k, I.p k * (f α * Hf α (P.frac j k))) volume 0 1 :=
    ii_sum Finset.univ (fun k α => I.p k * (f α * Hf α (P.frac j k)))
      (fun k _ => (hH k).1.const_mul _)
  have hgi : IntervalIntegrable g volume 0 1 := h1.add h2
  have hgv : ∫ α in (0:ℝ)..1, g α = P.idle j +
      ∑ k, I.p k * (P.frac j k * (Real.exp 1 / (Real.exp 1 - 1))) := by
    simp only [hg]
    rw [intervalIntegral.integral_add h1 h2]
    · rw [intervalIntegral.integral_finsetSum (fun k _ => (hH k).1.const_mul _)]
      rw [intervalIntegral.integral_mul_const]
      congr 1
      · have : ∫ α in (0:ℝ)..1, f α = 1 := by
          simp only [hf]
          rw [intervalIntegral.integral_div, integral_exp, Real.exp_zero]
          field_simp
        rw [this, one_mul]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [intervalIntegral.integral_const_mul, (hH k).2]
  have hpt : ∀ α ∈ Set.Ioc (0:ℝ) 1, f α * P.Calpha α j ≤ g α := by
    intro α hα
    have := Calpha_le P α hα.1 hα.2 j
    have e : g α = f α * (P.idle j + ∑ k, Hf α (P.frac j k) * I.p k) := by
      simp only [hg]
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this (hfpos α).le
  have hint : IntervalIntegrable (fun α => f α * P.Calpha α j) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one]
    have hgI : IntegrableOn g (Set.Ioc 0 1) volume := by
      have := hgi
      rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one] at this
      exact this
    refine Integrable.mono' hgI ?_ ?_
    · exact ((hfc.measurable.aemeasurable).mul (aemeas_Calpha P j)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun α hα => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpt α hα
      · exact mul_nonneg (hfpos α).le (listFinish_nonneg _ _)
  refine ⟨hint, ?_⟩
  have hle : ∫ α in (0:ℝ)..1, f α * P.Calpha α j ≤ ∫ α in (0:ℝ)..1, g α := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_mono_on hint.1 hgi.1 measurableSet_Ioc hpt
  refine hle.trans ?_
  rw [hgv, CP_decomp P j]
  have hidle : 0 ≤ P.idle j := ENNReal.toReal_nonneg
  have hr : 1 ≤ Real.exp 1 / (Real.exp 1 - 1) := by
    rw [le_div_iff₀ hE1]; linarith
  rw [mul_add, Finset.mul_sum]
  have : ∑ k, I.p k * (P.frac j k * (Real.exp 1 / (Real.exp 1 - 1))) =
      ∑ k, Real.exp 1 / (Real.exp 1 - 1) * (P.frac j k * I.p k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  nlinarith

end RAE_e5ddc447

open AvgCompletionSched.BestAlpha in
theorem solution {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (N : NonpreemptiveSchedule I) :
    IntervalIntegrable (fun α => Real.exp α / (Real.exp 1 - 1) * ∑ j, w j * P.Calpha α j)
        MeasureTheory.volume 0 1 ∧
      ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) * ∑ j, w j * P.Calpha α j
        ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, w j * N.C j := by
  have hfe : (fun α => Real.exp α / (Real.exp 1 - 1) * ∑ j, w j * P.Calpha α j) =
      fun α => ∑ j, w j * (Real.exp α / (Real.exp 1 - 1) * P.Calpha α j) := by
    funext α
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ := fun j => RAE_e5ddc447.job_bound P j
  have hI : ∀ j ∈ Finset.univ, IntervalIntegrable
      (fun α => w j * (Real.exp α / (Real.exp 1 - 1) * P.Calpha α j)) MeasureTheory.volume 0 1 :=
    fun j _ => (hJ j).1.const_mul _
  rw [hfe]
  refine ⟨RAE_e5ddc447.ii_sum _ _ hI, ?_⟩
  have hE : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hc : 0 ≤ Real.exp 1 / (Real.exp 1 - 1) := div_nonneg (Real.exp_pos 1).le (by linarith)
  have e1 : ∫ α in (0 : ℝ)..1, (∑ j, w j * (Real.exp α / (Real.exp 1 - 1) *
      P.Calpha α j)) = ∑ j, w j * ∫ α in (0 : ℝ)..1,
        Real.exp α / (Real.exp 1 - 1) * P.Calpha α j := by
    rw [intervalIntegral.integral_finsetSum hI]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [e1]
  calc ∑ j, w j * ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) * P.Calpha α j
      ≤ ∑ j, w j * (Real.exp 1 / (Real.exp 1 - 1) * P.CP j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hJ j).2 (hw j).le
    _ = Real.exp 1 / (Real.exp 1 - 1) * ∑ j, w j * P.CP j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, w j * (RAE_e5ddc447.ofNP N).CP j :=
        mul_le_mul_of_nonneg_left (hP _) hc
    _ ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, w j * N.C j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hc
        exact mul_le_mul_of_nonneg_left (RAE_e5ddc447.ofNP_CP N j) (hw j).le
