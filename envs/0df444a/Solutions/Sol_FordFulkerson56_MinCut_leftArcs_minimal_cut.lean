-- Prove2me | solution 1 for FordFulkerson56.MinCut.leftArcs_minimal_cut
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:31:16.790608+00:00
-- url     : https://prove2.me/submissions/deda9225-d4d2-4896-b65b-fce93d184550

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs



namespace FordFulkerson56.MinCut

section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma ff_load_add (f g : Finset E → ℝ) (e : E) : load (f + g) e = load f e + load g e := by
  simp [load, Finset.sum_add_distrib]

lemma ff_load_smul (c : ℝ) (f : Finset E → ℝ) (e : E) : load (c • f) e = c * load f e := by
  simp [load, Finset.mul_sum]

lemma ff_value_add (f g : Finset E → ℝ) : value (f + g) = value f + value g := by
  simp [value, Finset.sum_add_distrib]

lemma ff_value_smul (c : ℝ) (f : Finset E → ℝ) : value (c • f) = c * value f := by
  simp [value, Finset.mul_sum]

lemma ff_chain_nonempty (N : Network V E) {C : Finset E}
    (h : IsChain N N.source N.sink C) : C.Nonempty := by
  obtain ⟨p, vs, ⟨hl, hh, hlast, -⟩, rfl⟩ := h
  rcases p with _ | ⟨a, p⟩
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
    simp at hh hlast
    exact absurd (hh.symm.trans hlast) N.source_ne_sink
  · exact ⟨a, by simp⟩

lemma ff_le_load (f : Finset E → ℝ) (hf : ∀ C, 0 ≤ f C) {C : Finset E} {e : E} (he : e ∈ C) :
    f C ≤ load f e := by
  unfold load
  exact Finset.single_le_sum (f := f) (fun D _ => hf D) (by simp [he])

lemma ff_flow_le (N : Network V E) {f : Finset E → ℝ} (hf : IsFlow N f) (C : Finset E) :
    f C ≤ ∑ e, N.cap e := by
  by_cases h0 : f C = 0
  · rw [h0]; exact Finset.sum_nonneg (fun e _ => (N.cap_pos e).le)
  · obtain ⟨e, he⟩ := ff_chain_nonempty N (hf.2.1 C h0)
    calc f C ≤ load f e := ff_le_load f hf.1 he
      _ ≤ N.cap e := hf.2.2 e
      _ ≤ ∑ e, N.cap e := Finset.single_le_sum (fun e _ => (N.cap_pos e).le) (Finset.mem_univ e)

lemma ff_isClosed_flow (N : Network V E) : IsClosed {f : Finset E → ℝ | IsFlow N f} := by
  have h1 : IsClosed {f : Finset E → ℝ | ∀ C, 0 ≤ f C} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun C => isClosed_le continuous_const (continuous_apply C))
  have h2 : IsClosed {f : Finset E → ℝ | ∀ C, f C ≠ 0 → IsChain N N.source N.sink C} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun C => ?_)
    by_cases hC : IsChain N N.source N.sink C
    · simp [hC]
    · have : {f : Finset E → ℝ | f C ≠ 0 → IsChain N N.source N.sink C} = {f | f C = 0} := by
        ext f; simp [hC]
      rw [this]
      exact isClosed_eq (continuous_apply C) continuous_const
  have h3 : IsClosed {f : Finset E → ℝ | ∀ e, load f e ≤ N.cap e} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun e => isClosed_le ?_ continuous_const)
    unfold load
    exact continuous_finset_sum _ (fun C _ => continuous_apply C)
  have : {f : Finset E → ℝ | IsFlow N f} = {f : Finset E → ℝ | ∀ C, 0 ≤ f C} ∩
      ({f : Finset E → ℝ | ∀ C, f C ≠ 0 → IsChain N N.source N.sink C} ∩
        {f : Finset E → ℝ | ∀ e, load f e ≤ N.cap e}) := by
    ext f; simp [IsFlow]
  rw [this]
  exact h1.inter (h2.inter h3)

lemma ff_zero_flow (N : Network V E) : IsFlow N (0 : Finset E → ℝ) := by
  refine ⟨fun C => le_rfl, fun C h => absurd rfl h, fun e => ?_⟩
  simp [load]; exact (N.cap_pos e).le

lemma ff_exists_max (N : Network V E) : ∃ f, IsMaxFlow N f := by
  have hc : IsCompact {f : Finset E → ℝ | IsFlow N f} := by
    refine Metric.isCompact_of_isClosed_isBounded (ff_isClosed_flow N) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Finset E → ℝ)) (r := ∑ e, N.cap e)).subset ?_
    intro f hf
    have hM : 0 ≤ ∑ e, N.cap e := Finset.sum_nonneg (fun e _ => (N.cap_pos e).le)
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hM).2 (fun C => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf.1 C)]
    exact ff_flow_le N hf C
  have hv : Continuous (fun f : Finset E → ℝ => value f) := by
    unfold value
    exact continuous_finset_sum _ (fun C _ => continuous_apply C)
  obtain ⟨f, hf, hmax⟩ := hc.exists_isMaxOn ⟨0, ff_zero_flow N⟩ hv.continuousOn
  exact ⟨f, hf, fun g hg => hmax hg⟩

lemma ff_convex (N : Network V E) : Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} := by
  intro f hf g hg a b ha hb hab
  simp only [Set.mem_setOf_eq] at hf hg ⊢
  refine ⟨⟨fun C => ?_, fun C hC => ?_, fun e => ?_⟩, fun h hh => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hf.1.1 C; have := hg.1.1 C; positivity
  · by_cases h1 : f C = 0
    · by_cases h2 : g C = 0
      · simp [h1, h2] at hC
      · exact hg.1.2.1 C h2
    · exact hf.1.2.1 C h1
  · rw [ff_load_add, ff_load_smul, ff_load_smul]
    have h1 := mul_le_mul_of_nonneg_left (hf.1.2.2 e) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.1.2.2 e) hb
    have : a * N.cap e + b * N.cap e = N.cap e := by rw [← add_mul, hab, one_mul]
    linarith
  · rw [ff_value_add, ff_value_smul, ff_value_smul]
    have h1 := mul_le_mul_of_nonneg_left (hf.2 h hh) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.2 h hh) hb
    have : a * value h + b * value h = value h := by rw [← add_mul, hab, one_mul]
    linarith

theorem maxFlow_exists_convex_core (N : Network V E) :
    (∃ f, IsMaxFlow N f) ∧ Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} :=
  ⟨ff_exists_max N, ff_convex N⟩


inductive FFReach (N : Network V E) (A : Set E) (u : V) : V → Prop
  | refl : FFReach N A u u
  | step {x y : V} (e : E) : FFReach N A u x → e ∈ A →
      ((N.tail e = x ∧ N.head e = y) ∨ (N.head e = x ∧ N.tail e = y)) → FFReach N A u y

lemma ff_reach_mono (N : Network V E) {A B : Set E} {u w : V} (h : FFReach N A u w)
    (hAB : A ⊆ B) : FFReach N B u w := by
  induction h with
  | refl => exact FFReach.refl
  | step e _ he ho ih => exact FFReach.step e ih (hAB he) ho

lemma ff_reach_trans (N : Network V E) {A B : Set E} {u x y : V} (h1 : FFReach N A u x)
    (h2 : FFReach N B x y) : FFReach N (A ∪ B) u y := by
  induction h2 with
  | refl => exact ff_reach_mono N h1 Set.subset_union_left
  | step e _ he ho ih => exact FFReach.step e ih (Or.inr he) ho

lemma ff_walk_endpoint (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) {m : ℕ} (hm : m < p.length) {y : V}
    (hy : N.tail p[m] = y ∨ N.head p[m] = y) : y ∈ vs := by
  have := hw.2.2.2.2.2 m hm
  rcases hy with rfl | rfl <;> rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact List.mem_of_getElem? h1
  · exact List.mem_of_getElem? h2
  · exact List.mem_of_getElem? h2
  · exact List.mem_of_getElem? h1

lemma ff_walk_take (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) {k : ℕ} {y : V} (hk : vs[k]? = some y) :
    IsChainWalk N u y (p.take k) (vs.take (k + 1)) := by
  obtain ⟨hl, hh, hlast, hnv, hnp, hedge⟩ := hw
  have hkl : k < vs.length := by
    by_contra h; push_neg at h; rw [List.getElem?_eq_none h] at hk; simp at hk
  refine ⟨?_, ?_, ?_, hnv.sublist (List.take_sublist _ _), hnp.sublist (List.take_sublist _ _), ?_⟩
  · simp; omega
  · simp [List.head?_take, hh]
  · rw [List.getLast?_eq_getElem?]
    have : (List.take (k + 1) vs).length - 1 = k := by simp; omega
    rw [this, List.getElem?_take]; simp [hk]
  · intro i hi
    simp only [List.length_take] at hi
    have hi1 : i < k := by omega
    have hi2 : i < p.length := by omega
    have e1 : (p.take k)[i] = p[i] := List.getElem_take
    rw [e1, List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos (by omega)]
    exact hedge i hi2

lemma ff_reach_chain (N : Network V E) {A : Set E} {u w : V} (h : FFReach N A u w) :
    ∃ p vs, IsChainWalk N u w p vs ∧ ∀ x ∈ p, x ∈ A := by
  induction h with
  | refl =>
    refine ⟨[], [u], ⟨by simp, by simp, by simp, by simp, by simp, fun i hi => by simp at hi⟩, by simp⟩
  | @step x y e _ he ho ih =>
    obtain ⟨p, vs, hw, hA⟩ := ih
    by_cases hy : y ∈ vs
    · obtain ⟨k, hk, hk'⟩ := List.getElem_of_mem hy
      have hk2 : vs[k]? = some y := by rw [List.getElem?_eq_getElem hk, hk']
      exact ⟨_, _, ff_walk_take N hw hk2, fun z hz => hA z (List.mem_of_mem_take hz)⟩
    · obtain ⟨hl, hh, hlast, hnv, hnp, hedge⟩ := hw
      have hep : e ∉ p := by
        intro hep
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hep
        exact hy (ff_walk_endpoint N ⟨hl, hh, hlast, hnv, hnp, hedge⟩ hm
          (by rcases ho with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]))
      refine ⟨p ++ [e], vs ++ [y], ⟨by simp [hl], ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
      · have : vs ≠ [] := by intro h; simp [h] at hl
        rw [List.head?_append, hh]; rfl
      · rw [List.nodup_append]; refine ⟨hnv, by simp, ?_⟩
        simp; intro a ha h; exact hy (h ▸ ha)
      · rw [List.nodup_append]; refine ⟨hnp, by simp, ?_⟩
        simp; intro a ha h; exact hep (h ▸ ha)
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [List.getElem_append_left hi, List.getElem?_append_left (by omega),
            List.getElem?_append_left (by omega)]
          exact hedge i hi
        · rw [List.getElem_append_right (by omega)]
          rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
          have hx : vs[p.length]? = some x := by
            rw [List.getLast?_eq_getElem?, hl] at hlast; simpa using hlast
          simp only [hx, Nat.sub_self, List.getElem_singleton]
          have : p.length + 1 - vs.length = 0 := by omega
          rw [this]
          rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; simp [h1, h2]
          · right; simp [h1, h2]
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hA z hz
        · simp at hz; exact hz ▸ he

/-- arcs of a walk between indices -/
def ffSeg (p : List E) (i k : ℕ) : Set E := {x | ∃ j, i ≤ j ∧ j < k ∧ p[j]? = some x}

lemma ff_walk_reach (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (i : ℕ) :
    ∀ k a b, i ≤ k → k ≤ p.length → vs[i]? = some a → vs[k]? = some b →
      FFReach N (ffSeg p i k) a b := by
  intro k
  induction k with
  | zero =>
    intro a b hik _ ha hb
    have : i = 0 := by omega
    subst this
    rw [ha] at hb; cases hb; exact FFReach.refl
  | succ k ih =>
    intro a b hik hkp ha hb
    rcases Nat.lt_or_ge k i with h | h
    · have : i = k + 1 := by omega
      subst this
      rw [ha] at hb; cases hb; exact FFReach.refl
    · obtain ⟨c, hc⟩ : ∃ c, vs[k]? = some c := by
        have : k < vs.length := by have := hw.1; omega
        exact ⟨vs[k], List.getElem?_eq_getElem this⟩
      have h1 := ih a c h (by omega) ha hc
      have hkp' : k < p.length := by omega
      refine FFReach.step p[k] (ff_reach_mono N h1 ?_) ?_ ?_
      · rintro x ⟨j, hj1, hj2, hj3⟩; exact ⟨j, hj1, by omega, hj3⟩
      · exact ⟨k, h, by omega, List.getElem?_eq_getElem hkp'⟩
      · rcases hw.2.2.2.2.2 k hkp' with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · rw [hc] at h3; rw [hb] at h4
          left; exact ⟨(Option.some_inj.mp h3).symm, (Option.some_inj.mp h4).symm⟩
        · rw [hc] at h3; rw [hb] at h4
          right; exact ⟨(Option.some_inj.mp h3).symm, (Option.some_inj.mp h4).symm⟩

lemma ff_walk_last (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) : vs[p.length]? = some w := by
  have h := hw.2.2.1
  rw [List.getLast?_eq_getElem?, hw.1] at h; simpa using h

lemma ff_walk_first (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) : vs[0]? = some u := by
  have h := hw.2.1
  rw [List.head?_eq_getElem?] at h; exact h

lemma ff_seg_sub (p : List E) (i k : ℕ) : ffSeg p i k ⊆ {x | x ∈ p} := by
  rintro x ⟨j, -, -, hj⟩; exact List.mem_of_getElem? hj

lemma ff_seg_nodup {p : List E} (hp : p.Nodup) {i k j : ℕ} {x : E} (hx : x ∈ ffSeg p i k)
    (hj : p[j]? = some x) : i ≤ j ∧ j < k := by
  obtain ⟨j', h1, h2, h3⟩ := hx
  have hj'l : j' < p.length := by
    by_contra h; push_neg at h; rw [List.getElem?_eq_none h] at h3; simp at h3
  have hjl : j < p.length := by
    by_contra h; push_neg at h; rw [List.getElem?_eq_none h] at hj; simp at hj
  have : j = j' := by
    rw [List.getElem?_eq_getElem hjl] at hj; rw [List.getElem?_eq_getElem hj'l] at h3
    have := (hj.trans h3.symm)
    exact (hp.getElem_inj_iff).mp (Option.some_inj.mp this)
  subst this; exact ⟨h1, h2⟩

def ffInd (C : Finset E) : Finset E → ℝ := fun D => if D = C then 1 else 0

lemma ff_load_ind (C : Finset E) (e : E) : load (ffInd C) e = if e ∈ C then 1 else 0 := by
  unfold load ffInd
  rw [Finset.sum_ite_eq']; simp

lemma ff_value_ind (C : Finset E) : value (ffInd C) = 1 := by
  unfold value ffInd; simp

lemma ff_half_max (N : Network V E) {f g : Finset E → ℝ} (hf : IsMaxFlow N f)
    (hg : IsMaxFlow N g) : IsMaxFlow N ((1/2 : ℝ) • f + (1/2 : ℝ) • g) :=
  ff_convex N hf hg (by norm_num) (by norm_num) (by norm_num)

lemma ff_load_half (f g : Finset E → ℝ) (e : E) :
    load ((1/2 : ℝ) • f + (1/2 : ℝ) • g) e = (load f e + load g e) / 2 := by
  rw [ff_load_add, ff_load_smul, ff_load_smul]; ring

lemma ff_unsat_lt (N : Network V E) {f : Finset E → ℝ} (hf : IsFlow N f) {e : E}
    (h : ¬ Saturated N f e) : load f e < N.cap e :=
  lt_of_le_of_ne (hf.2.2 e) h

lemma ff_generic (N : Network V E) (T : Finset E)
    (hT : ∀ e ∈ T, ∃ f, IsMaxFlow N f ∧ load f e < N.cap e) :
    ∃ g, IsMaxFlow N g ∧ ∀ e ∈ T, load g e < N.cap e := by
  induction T using Finset.induction_on with
  | empty => obtain ⟨g, hg⟩ := ff_exists_max N; exact ⟨g, hg, by simp⟩
  | insert a T ha ih =>
    obtain ⟨g, hg, hgT⟩ := ih (fun e he => hT e (Finset.mem_insert_of_mem he))
    obtain ⟨f, hf, hfa⟩ := hT a (Finset.mem_insert_self a T)
    refine ⟨_, ff_half_max N hg hf, fun e he => ?_⟩
    rw [ff_load_half]
    have h1 := hg.1.2.2 e; have h2 := hf.1.2.2 e
    rcases Finset.mem_insert.mp he with rfl | he
    · linarith
    · have := hgT e he; linarith

lemma ff_slack (T : Finset E) (s : E → ℝ) (hs : ∀ e ∈ T, 0 < s e) :
    ∃ δ > 0, ∀ e ∈ T, δ ≤ s e := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih (fun e he => hs e (Finset.mem_insert_of_mem he))
    refine ⟨min δ (s a), lt_min hδ (hs a (Finset.mem_insert_self a T)), fun e he => ?_⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h e he)

/-- generic maximal flow: unsaturated on every arc outside the saturated set, with uniform slack -/
lemma ff_generic_S (N : Network V E) :
    ∃ g, IsMaxFlow N g ∧ ∃ δ > 0, ∀ e, e ∉ saturatedSet N → load g e + δ ≤ N.cap e := by
  classical
  obtain ⟨g, hg, hlt⟩ := ff_generic N (Finset.univ.filter (fun e => e ∉ saturatedSet N)) (by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    unfold saturatedSet at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at he
    obtain ⟨f, hf, hs⟩ := he
    exact ⟨f, hf, ff_unsat_lt N hf.1 hs⟩)
  obtain ⟨δ, hδ, h⟩ := ff_slack (Finset.univ.filter (fun e => e ∉ saturatedSet N))
    (fun e => N.cap e - load g e) (fun e he => by have := hlt e he; linarith)
  refine ⟨g, hg, δ, hδ, fun e he => ?_⟩
  have := h e (by simp [he]); linarith

lemma ff_mem_S (N : Network V E) {e : E} (he : e ∈ saturatedSet N) {f : Finset E → ℝ}
    (hf : IsMaxFlow N f) : load f e = N.cap e := by
  unfold saturatedSet at he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  exact he f hf

/-- rerouting: removing `ε` from chain flow `C` and adding `ε` to chain `P` -/
lemma ff_reroute (N : Network V E) {g : Finset E → ℝ} (hg : IsMaxFlow N g) {C P : Finset E}
    {ε : ℝ} (hε : 0 < ε) (hC : ε ≤ g C) (hP : IsChain N N.source N.sink P)
    (hload : ∀ x, x ∈ P → x ∉ C → load g x + ε ≤ N.cap x) :
    IsMaxFlow N (g + (-ε) • ffInd C + ε • ffInd P) := by
  have hv : value (g + (-ε) • ffInd C + ε • ffInd P) = value g := by
    rw [ff_value_add, ff_value_add, ff_value_smul, ff_value_smul, ff_value_ind, ff_value_ind]; ring
  refine ⟨⟨fun D => ?_, fun D hD => ?_, fun x => ?_⟩, fun h hh => hv ▸ hg.2 h hh⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ffInd]
    have := hg.1.1 D
    split_ifs with h1 h2 <;> subst_vars <;> nlinarith
  · by_cases hDP : D = P
    · exact hDP ▸ hP
    · apply hg.1.2.1 D
      intro h0
      apply hD
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ffInd, if_neg hDP, h0]
      split_ifs with h1
      · subst h1; linarith
      · ring
  · rw [ff_load_add, ff_load_add, ff_load_smul, ff_load_smul, ff_load_ind, ff_load_ind]
    have := hg.1.2.2 x
    by_cases h1 : x ∈ P <;> by_cases h2 : x ∈ C <;> simp [h1, h2]
    · linarith
    · linarith [hload x h1 h2]
    · linarith
    · linarith

lemma ff_load_reroute (g : Finset E → ℝ) (C P : Finset E) (ε : ℝ) (x : E) (h1 : x ∈ C)
    (h2 : x ∉ P) : load (g + (-ε) • ffInd C + ε • ffInd P) x = load g x - ε := by
  rw [ff_load_add, ff_load_add, ff_load_smul, ff_load_smul, ff_load_ind, ff_load_ind]
  simp [h1, h2]; ring

lemma ff_walk_edge (N : Network V E) {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) {m : ℕ} {e : E} (hm : p[m]? = some e) :
    ∃ a b, vs[m]? = some a ∧ vs[m+1]? = some b ∧
      ((a = N.tail e ∧ b = N.head e) ∨ (a = N.head e ∧ b = N.tail e)) := by
  obtain ⟨hml, rfl⟩ := List.getElem?_eq_some_iff.mp hm
  rcases hw.2.2.2.2.2 m hml with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, _, h1, h2, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, h1, h2, Or.inr ⟨rfl, rfl⟩⟩

lemma ff_mem_leftArcs (N : Network V E) (e : E) : e ∈ leftArcs N ↔ e ∈ saturatedSet N ∧
    ∃ v, IsLeftVertex N e v ∧
      ∃ f, IsMaxFlow N f ∧ ∃ C, IsChain N N.source v C ∧ ∀ e' ∈ C, ¬ Saturated N f e' := by
  unfold leftArcs
  simp only [Finset.mem_filter]

theorem lemma1_core (N : Network V E) : IsDisconnecting N (saturatedSet N) := by
  intro C hC
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hCS : ∀ e ∈ C, e ∉ saturatedSet N := fun e he hS => by
    have : e ∈ C ∩ saturatedSet N := Finset.mem_inter.mpr ⟨he, hS⟩
    rw [hne] at this; simp at this
  obtain ⟨g, hg, δ, hδ, hgδ⟩ := ff_generic_S N
  have hflow : IsFlow N (g + δ • ffInd C) := by
    refine ⟨fun D => ?_, fun D hD => ?_, fun x => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ffInd]
      have := hg.1.1 D; split_ifs <;> nlinarith
    · by_cases hDC : D = C
      · exact hDC ▸ hC
      · apply hg.1.2.1 D; simpa [ffInd, hDC] using hD
    · rw [ff_load_add, ff_load_smul, ff_load_ind]
      by_cases hx : x ∈ C
      · simp [hx]; exact hgδ x (hCS x hx)
      · simp [hx]; exact hg.1.2.2 x
  have := hg.2 _ hflow
  rw [ff_value_add, ff_value_smul, ff_value_ind] at this
  linarith

theorem lemma2_core (N : Network V E) : IsDisconnecting N (leftArcs N) := by
  classical
  intro C hC
  have h1 := lemma1_core N C hC
  obtain ⟨p, vs, hw, rfl⟩ := hC
  have hex : ∃ i : ℕ, ∃ e : E, p[i]? = some e ∧ e ∈ saturatedSet N := by
    obtain ⟨e, he⟩ := h1
    rw [Finset.mem_inter, List.mem_toFinset] at he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he.1
    exact ⟨i, _, List.getElem?_eq_getElem hi, he.2⟩
  obtain ⟨e, hei, heS⟩ := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, ∀ x, p[j]? = some x → x ∉ saturatedSet N :=
    fun j hj x hx hxS => Nat.find_min hex hj ⟨x, hx, hxS⟩
  have hil : Nat.find hex < p.length := (List.getElem?_eq_some_iff.mp hei).1
  obtain ⟨a, b, ha, hb, hab⟩ := ff_walk_edge N hw hei
  have hreach1 := ff_walk_reach N hw 0 (Nat.find hex) N.source a (Nat.zero_le _) hil.le
    (ff_walk_first N hw) ha
  have hseg1 : ∀ x ∈ ffSeg p 0 (Nat.find hex), x ∉ saturatedSet N := by
    rintro x ⟨j, -, hj, hx⟩; exact hmin j hj x hx
  obtain ⟨g, hg, δ, hδ, hgδ⟩ := ff_generic_S N
  obtain ⟨C', hC'pos, heC'⟩ : ∃ C', 0 < g C' ∧ e ∈ C' := by
    by_contra hcon
    push_neg at hcon
    have h0 : load g e = 0 := by
      unfold load
      apply Finset.sum_eq_zero
      intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      exact le_antisymm (not_lt.mp fun h => hcon D h hD) (hg.1.1 D)
    have := ff_mem_S N heS hg
    linarith [N.cap_pos e]
  obtain ⟨p', vs', hw', hp'⟩ := hg.1.2.1 C' hC'pos.ne'
  subst hp'
  obtain ⟨m, hm, hme⟩ := List.getElem_of_mem (List.mem_toFinset.mp heC')
  have hme' : p'[m]? = some e := by rw [List.getElem?_eq_getElem hm, hme]
  obtain ⟨a', b', ha', hb', hab'⟩ := ff_walk_edge N hw' hme'
  by_cases haa : a' = a
  · refine ⟨e, Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (List.mem_of_getElem? hei), ?_⟩⟩
    rw [ff_mem_leftArcs]
    refine ⟨heS, a, ⟨g, hg, p', vs', hw', hC'pos, m, hme', haa ▸ ha'⟩, g, hg, ?_⟩
    obtain ⟨p3, vs3, hw3, h3⟩ := ff_reach_chain N hreach1
    refine ⟨p3.toFinset, ⟨p3, vs3, hw3, rfl⟩, fun x hx hsat => ?_⟩
    have := hgδ x (hseg1 x (h3 x (List.mem_toFinset.mp hx)))
    unfold Saturated at hsat; linarith
  · exfalso
    have hba : b' = a := by
      have := N.tail_ne_head e
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    subst hba
    have hreach2 := ff_walk_reach N hw' (m+1) p'.length b' N.sink (by omega) le_rfl hb'
      (ff_walk_last N hw')
    have hreach := ff_reach_trans N hreach1 hreach2
    obtain ⟨p3, vs3, hw3, h3⟩ := ff_reach_chain N hreach
    have hε : 0 < min (g p'.toFinset) δ := lt_min hC'pos hδ
    have hmax := ff_reroute N hg (P := p3.toFinset) hε (min_le_left _ _) ⟨p3, vs3, hw3, rfl⟩ (by
      intro x hxP hxC
      rcases h3 x (List.mem_toFinset.mp hxP) with hx | hx
      · linarith [hgδ x (hseg1 x hx), min_le_right (g p'.toFinset) δ]
      · exact absurd (List.mem_toFinset.mpr (ff_seg_sub p' _ _ hx)) hxC)
    have heP : e ∉ p3.toFinset := by
      intro hx
      rcases h3 e (List.mem_toFinset.mp hx) with hx | hx
      · exact hseg1 e hx heS
      · have := ff_seg_nodup hw'.2.2.2.2.1 hx hme'; omega
    have h1 := ff_load_reroute g p'.toFinset p3.toFinset (min (g p'.toFinset) δ) e heC' heP
    have h2 := ff_mem_S N heS hmax
    have h3 := ff_mem_S N heS hg
    linarith

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma ff_ind_ineq (P Q C1 C2 a1 b1 a2 b2 : Prop) [Decidable P] [Decidable Q] [Decidable C1]
    [Decidable C2] (hP : P → a1 ∨ b2) (hQ : Q → a2 ∨ b1) (h1 : ¬(a1 ∧ b1)) (h2 : ¬ (a2 ∧ b2))
    (hc1 : a1 ∨ b1 → C1) (hc2 : a2 ∨ b2 → C2) :
    (if P then (1:ℝ) else 0) + (if Q then 1 else 0) ≤
      (if C1 then 1 else 0) + (if C2 then 1 else 0) := by
  split_ifs <;> norm_num <;> tauto

lemma ff_seg_disj {p : List E} (hp : p.Nodup) {i : ℕ} {x : E} (h1 : x ∈ ffSeg p 0 i)
    (h2 : x ∈ ffSeg p (i+1) p.length) : False := by
  obtain ⟨j, -, hj, hx⟩ := h1
  have := ff_seg_nodup hp h2 hx
  omega

theorem leftVertex_unique_core (N : Network V E) :
    ∀ e ∈ saturatedSet N, ∀ v w : V, IsLeftVertex N e v → IsLeftVertex N e w → v = w := by
  intro e heS v w hv hw
  by_contra hvw
  obtain ⟨f1, hf1, p1, vs1, hw1, hpos1, i, hi, hvi⟩ := hv
  obtain ⟨f2, hf2, p2, vs2, hw2, hpos2, j, hj, hwj⟩ := hw
  obtain ⟨a, b, ha, hb, hab⟩ := ff_walk_edge N hw1 hi
  obtain ⟨a', b', ha', hb', hab'⟩ := ff_walk_edge N hw2 hj
  have hav : a = v := by rw [hvi] at ha; exact (Option.some_inj.mp ha).symm
  have haw : a' = w := by rw [hwj] at ha'; exact (Option.some_inj.mp ha').symm
  subst a; subst a'
  have hbw : b = w ∧ b' = v := by
    have := N.tail_ne_head e
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all
  obtain ⟨hbw1, hbw2⟩ := hbw
  subst b; subst b'
  have hil : i < p1.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < p2.length := (List.getElem?_eq_some_iff.mp hj).1
  -- P : source → v → sink
  have rP := ff_reach_trans N
    (ff_walk_reach N hw1 0 i N.source v (Nat.zero_le _) hil.le (ff_walk_first N hw1) hvi)
    (ff_walk_reach N hw2 (j+1) p2.length v N.sink (by omega) le_rfl hb' (ff_walk_last N hw2))
  have rQ := ff_reach_trans N
    (ff_walk_reach N hw2 0 j N.source w (Nat.zero_le _) hjl.le (ff_walk_first N hw2) hwj)
    (ff_walk_reach N hw1 (i+1) p1.length w N.sink (by omega) le_rfl hb (ff_walk_last N hw1))
  obtain ⟨pP, vsP, hwP, hP⟩ := ff_reach_chain N rP
  obtain ⟨pQ, vsQ, hwQ, hQ⟩ := ff_reach_chain N rQ
  set h := (1/2 : ℝ) • f1 + (1/2 : ℝ) • f2 with hh
  have hmax := ff_half_max N hf1 hf2
  rw [← hh] at hmax
  set C1 := p1.toFinset
  set C2 := p2.toFinset
  set P := pP.toFinset
  set Q := pQ.toFinset
  have hC1 : 0 < h C1 := by
    simp only [hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hf2.1.1 C1]
  have hC2 : 0 < h C2 := by
    simp only [hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hf1.1.1 C2]
  set ε := min (h C1) (h C2) / 2 with hεdef
  have hε : 0 < ε := by have := lt_min hC1 hC2; linarith
  have hε1 : ε ≤ h C1 / 2 := by have := min_le_left (h C1) (h C2); linarith
  have hε2 : ε ≤ h C2 / 2 := by have := min_le_right (h C1) (h C2); linarith
  set h' := h + (-ε) • ffInd C1 + (-ε) • ffInd C2 + ε • ffInd P + ε • ffInd Q with hh'
  have hload : ∀ x, load h' x = load h x - ε * (if x ∈ C1 then 1 else 0)
      - ε * (if x ∈ C2 then 1 else 0) + ε * (if x ∈ P then 1 else 0)
      + ε * (if x ∈ Q then 1 else 0) := by
    intro x
    rw [hh', ff_load_add, ff_load_add, ff_load_add, ff_load_add, ff_load_smul, ff_load_smul,
      ff_load_smul, ff_load_smul, ff_load_ind, ff_load_ind, ff_load_ind, ff_load_ind]
    ring
  have hP' : IsChain N N.source N.sink P := ⟨pP, vsP, hwP, rfl⟩
  have hQ' : IsChain N N.source N.sink Q := ⟨pQ, vsQ, hwQ, rfl⟩
  have hnn : ∀ D, h D - ε * (if D = C1 then 1 else 0) - ε * (if D = C2 then 1 else 0) ≥ 0 := by
    intro D
    have := hmax.1.1 D
    split_ifs with h1 h2 <;> subst_vars <;> linarith
  have hmax' : IsMaxFlow N h' := by
    have hv : value h' = value h := by
      rw [hh', ff_value_add, ff_value_add, ff_value_add, ff_value_add, ff_value_smul, ff_value_smul,
        ff_value_smul, ff_value_smul, ff_value_ind, ff_value_ind, ff_value_ind, ff_value_ind]; ring
    have hD : ∀ D, h' D = h D - ε * (if D = C1 then 1 else 0) - ε * (if D = C2 then 1 else 0)
        + ε * (if D = P then 1 else 0) + ε * (if D = Q then 1 else 0) := by
      intro D; simp only [hh', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ffInd]; ring
    refine ⟨⟨fun D => ?_, fun D hD0 => ?_, fun x => ?_⟩, fun g hg => hv ▸ hmax.2 g hg⟩
    · rw [hD]; have := hnn D
      have : ε * (if D = P then 1 else 0) ≥ 0 := by split_ifs <;> linarith
      have : ε * (if D = Q then 1 else 0) ≥ 0 := by split_ifs <;> linarith
      linarith
    · by_cases hDP : D = P
      · exact hDP ▸ hP'
      by_cases hDQ : D = Q
      · exact hDQ ▸ hQ'
      apply hmax.1.2.1 D
      intro h0
      apply hD0
      rw [hD, h0, if_neg hDP, if_neg hDQ]
      have n1 : D ≠ C1 := fun h1 => by rw [h1] at h0; linarith
      have n2 : D ≠ C2 := fun h1 => by rw [h1] at h0; linarith
      rw [if_neg n1, if_neg n2]; ring
    · rw [hload x]
      have hcap := hmax.1.2.2 x
      have hind := ff_ind_ineq (x ∈ P) (x ∈ Q) (x ∈ C1) (x ∈ C2)
        (x ∈ ffSeg p1 0 i) (x ∈ ffSeg p1 (i+1) p1.length)
        (x ∈ ffSeg p2 0 j) (x ∈ ffSeg p2 (j+1) p2.length)
        (fun hx => hP x (List.mem_toFinset.mp hx)) (fun hx => hQ x (List.mem_toFinset.mp hx))
        (fun ⟨h1, h2⟩ => ff_seg_disj hw1.2.2.2.2.1 h1 h2)
        (fun ⟨h1, h2⟩ => ff_seg_disj hw2.2.2.2.2.1 h1 h2)
        (fun hx => List.mem_toFinset.mpr (by rcases hx with hx | hx <;> exact ff_seg_sub p1 _ _ hx))
        (fun hx => List.mem_toFinset.mpr (by rcases hx with hx | hx <;> exact ff_seg_sub p2 _ _ hx))
      nlinarith
  have heC1 : e ∈ C1 := List.mem_toFinset.mpr (List.mem_of_getElem? hi)
  have heC2 : e ∈ C2 := List.mem_toFinset.mpr (List.mem_of_getElem? hj)
  have heP : e ∉ P := by
    intro hx
    rcases hP e (List.mem_toFinset.mp hx) with hx | hx
    · have := ff_seg_nodup hw1.2.2.2.2.1 hx hi; omega
    · have := ff_seg_nodup hw2.2.2.2.2.1 hx hj; omega
  have heQ : e ∉ Q := by
    intro hx
    rcases hQ e (List.mem_toFinset.mp hx) with hx | hx
    · have := ff_seg_nodup hw2.2.2.2.2.1 hx hj; omega
    · have := ff_seg_nodup hw1.2.2.2.2.1 hx hi; omega
  have e1 := hload e
  rw [if_pos heC1, if_pos heC2, if_neg heP, if_neg heQ] at e1
  have e2 := ff_mem_S N heS hmax'
  have e3 := ff_mem_S N heS hmax
  linarith

lemma ff_two_left_core (N : Network V E) {f : Finset E → ℝ} (hf : IsMaxFlow N f)
    {p : List E} {vs : List V} (hw : IsChainWalk N N.source N.sink p vs)
    (hpos : 0 < f p.toFinset) {i1 i2 : ℕ} {e1 e2 : E} (h1 : p[i1]? = some e1)
    (h2 : p[i2]? = some e2) (h12 : i1 < i2) (he1 : e1 ∈ leftArcs N) (he2 : e2 ∈ leftArcs N) :
    False := by
  rw [ff_mem_leftArcs] at he1 he2
  have he1S := he1.1
  obtain ⟨he2S, v, hv, f2, hf2, Q, ⟨q, qs, hwq, rfl⟩, hQ⟩ := he2
  obtain ⟨a, b, ha, hb, -⟩ := ff_walk_edge N hw h2
  have hav : a = v := leftVertex_unique_core N e2 he2S a v
    ⟨f, hf, p, vs, hw, hpos, i2, h2, ha⟩ hv
  subst hav
  have hi2 : i2 < p.length := (List.getElem?_eq_some_iff.mp h2).1
  have rP := ff_reach_trans N
    (ff_walk_reach N hwq 0 q.length N.source a (Nat.zero_le _) le_rfl (ff_walk_first N hwq)
      (ff_walk_last N hwq))
    (ff_walk_reach N hw i2 p.length a N.sink hi2.le le_rfl ha (ff_walk_last N hw))
  obtain ⟨pP, vsP, hwP, hP⟩ := ff_reach_chain N rP
  have hmax := ff_half_max N hf hf2
  set h := (1/2 : ℝ) • f + (1/2 : ℝ) • f2 with hh
  have hC : 0 < h p.toFinset := by
    simp only [hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hf2.1.1 p.toFinset]
  obtain ⟨δ, hδ, hδQ⟩ := ff_slack q.toFinset (fun x => N.cap x - load h x) (by
    intro x hx
    have := ff_unsat_lt N hf2.1 (hQ x hx)
    have := hf.1.2.2 x
    rw [hh, ff_load_half]; linarith)
  have hε : 0 < min (h p.toFinset) δ := lt_min hC hδ
  have hmax' := ff_reroute N hmax (P := pP.toFinset) hε (min_le_left _ _) ⟨pP, vsP, hwP, rfl⟩ (by
    intro x hxP hxC
    rcases hP x (List.mem_toFinset.mp hxP) with hx | hx
    · have := hδQ x (List.mem_toFinset.mpr (ff_seg_sub q _ _ hx))
      have := min_le_right (h p.toFinset) δ
      linarith
    · exact absurd (List.mem_toFinset.mpr (ff_seg_sub p _ _ hx)) hxC)
  have he1C : e1 ∈ p.toFinset := List.mem_toFinset.mpr (List.mem_of_getElem? h1)
  have he1P : e1 ∉ pP.toFinset := by
    intro hx
    rcases hP e1 (List.mem_toFinset.mp hx) with hx | hx
    · exact hQ e1 (List.mem_toFinset.mpr (ff_seg_sub q _ _ hx)) (ff_mem_S N he1S hf2)
    · have := ff_seg_nodup hw.2.2.2.2.1 hx h1; omega
  have e1 := ff_load_reroute h p.toFinset pP.toFinset (min (h p.toFinset) δ) e1 he1C he1P
  have e2 := ff_mem_S N he1S hmax'
  have e3 := ff_mem_S N he1S hmax
  linarith

theorem lemma3_core (N : Network V E) :
    ∀ f, IsMaxFlow N f → ∀ C : Finset E, 0 < f C → (C ∩ leftArcs N).card ≤ 1 := by
  intro f hf C hC
  by_contra hcard
  push_neg at hcard
  obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_inter] at he1 he2
  obtain ⟨p, vs, hw, rfl⟩ := hf.1.2.1 _ hC.ne'
  obtain ⟨i1, hi1, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp he1.1)
  obtain ⟨i2, hi2, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp he2.1)
  rcases lt_trichotomy i1 i2 with h | h | h
  · exact ff_two_left_core N hf hw hC (List.getElem?_eq_getElem hi1)
      (List.getElem?_eq_getElem hi2) h he1.2 he2.2
  · subst h; exact hne rfl
  · exact ff_two_left_core N hf hw hC (List.getElem?_eq_getElem hi2)
      (List.getElem?_eq_getElem hi1) h he2.2 he1.2

lemma ff_sum_load (f : Finset E → ℝ) (D : Finset E) :
    ∑ e ∈ D, load f e = ∑ C, f C * ((C ∩ D).card : ℝ) := by
  unfold load
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have : D.filter (fun a => a ∈ C) = C ∩ D := by ext e; simp [and_comm]
  rw [this]

lemma ff_value_le_cut (N : Network V E) {f : Finset E → ℝ} (hf : IsFlow N f) {D : Finset E}
    (hD : IsDisconnecting N D) : value f ≤ cutValue N D := by
  calc value f = ∑ C, f C := rfl
    _ ≤ ∑ C, f C * ((C ∩ D).card : ℝ) := by
      refine Finset.sum_le_sum (fun C _ => ?_)
      by_cases h0 : f C = 0
      · simp [h0]
      · have hne := hD C (hf.2.1 C h0)
        have : (1 : ℝ) ≤ ((C ∩ D).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hne
        nlinarith [hf.1 C]
    _ = ∑ e ∈ D, load f e := (ff_sum_load f D).symm
    _ ≤ ∑ e ∈ D, N.cap e := Finset.sum_le_sum (fun e _ => hf.2.2 e)

lemma ff_value_eq_L (N : Network V E) {f : Finset E → ℝ} (hf : IsMaxFlow N f) :
    value f = cutValue N (leftArcs N) := by
  have hL := lemma2_core N
  calc value f = ∑ C, f C := rfl
    _ = ∑ C, f C * ((C ∩ leftArcs N).card : ℝ) := by
      refine Finset.sum_congr rfl (fun C _ => ?_)
      by_cases h0 : f C = 0
      · simp [h0]
      · have hne := hL C (hf.1.2.1 C h0)
        have h1 := lemma3_core N f hf C (lt_of_le_of_ne (hf.1.1 C) (Ne.symm h0))
        have : (C ∩ leftArcs N).card = 1 := le_antisymm h1 (Finset.card_pos.mpr hne)
        simp [this]
    _ = ∑ e ∈ leftArcs N, load f e := (ff_sum_load f _).symm
    _ = ∑ e ∈ leftArcs N, N.cap e := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [ff_mem_leftArcs] at he
      exact ff_mem_S N he.1 hf

theorem leftArcs_minimal_cut_core (N : Network V E) :
    IsCut N (leftArcs N) ∧
    (∀ D : Finset E, IsDisconnecting N D → cutValue N (leftArcs N) ≤ cutValue N D) ∧
    ∀ f, IsMaxFlow N f → value f = cutValue N (leftArcs N) := by
  obtain ⟨f, hf⟩ := ff_exists_max N
  have hmin : ∀ D : Finset E, IsDisconnecting N D → cutValue N (leftArcs N) ≤ cutValue N D :=
    fun D hD => (ff_value_eq_L N hf) ▸ ff_value_le_cut N hf.1 hD
  refine ⟨⟨lemma2_core N, fun D' hD' hdisc => ?_⟩, hmin, fun g hg => ff_value_eq_L N hg⟩
  have h1 := hmin D' hdisc
  obtain ⟨i, hi, hni⟩ := Finset.exists_of_ssubset hD'
  have h2 : cutValue N D' < cutValue N (leftArcs N) :=
    Finset.sum_lt_sum_of_subset hD'.1 hi hni (N.cap_pos i) (fun j _ _ => (N.cap_pos j).le)
  linarith
end
end FordFulkerson56.MinCut

open FordFulkerson56.MinCut


theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    IsCut N (leftArcs N) ∧
    (∀ D : Finset E, IsDisconnecting N D → cutValue N (leftArcs N) ≤ cutValue N D) ∧
    ∀ f, IsMaxFlow N f → value f = cutValue N (leftArcs N) := by
  exact leftArcs_minimal_cut_core N
