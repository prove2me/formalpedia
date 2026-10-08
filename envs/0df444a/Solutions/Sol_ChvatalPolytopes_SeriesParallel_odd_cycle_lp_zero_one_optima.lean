-- Prove2me | solution 1 for ChvatalPolytopes.SeriesParallel.odd_cycle_lp_zero_one_optima
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T19:30:58.714491+00:00
-- url     : https://prove2.me/submissions/671de0a3-5f21-47f7-921c-b1414cbf7777

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_OddCycleLP
import Definitions.Def_ChvatalPolytopes_SeriesParallel_CircuitCover
import Definitions.Def_ChvatalPolytopes_SeriesParallel_deleteIdentify

set_option autoImplicit false

/- Complete checked body: DirectedWalk -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

inductive DirectedWalk {V : Type*} (R : V → V → Prop) : V → V → Type _
  | nil (v : V) : DirectedWalk R v v
  | cons {a b c : V} : R a b → DirectedWalk R b c → DirectedWalk R a c

namespace DirectedWalk

variable {V : Type*} {R : V → V → Prop}

def support : {a b : V} → DirectedWalk R a b → List V
  | a, _, .nil _ => [a]
  | a, _, .cons _ p => a :: p.support

def IsSimple {a b : V} (p : DirectedWalk R a b) : Prop := p.support.Nodup

theorem start_mem {a b : V} (p : DirectedWalk R a b) : a ∈ p.support := by
  cases p <;> simp [support]

theorem end_mem {a b : V} (p : DirectedWalk R a b) : b ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons h p ih => simp [support, ih]

def append {a b c : V} : DirectedWalk R a b → DirectedWalk R b c → DirectedWalk R a c
  | .nil _, q => q
  | .cons h p, q => .cons h (append p q)

theorem simple_suffix {a b : V} (p : DirectedWalk R a b) (hp : p.IsSimple)
    (v : V) (hv : v ∈ p.support) :
    ∃ q : DirectedWalk R v b, q.IsSimple ∧ ∀ w ∈ q.support, w ∈ p.support := by
  induction p with
  | nil a =>
    have he : v = a := by simpa [support] using hv
    subst v
    exact ⟨.nil a, by simp [IsSimple, support], fun _ hw => hw⟩
  | @cons a b c hab p ih =>
    have hnodup : a ∉ p.support ∧ p.support.Nodup := by
      simpa [IsSimple, support] using hp
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact ⟨.cons hab p, hp, fun _ hw => hw⟩
    · obtain ⟨q, hq, hsub⟩ := ih hnodup.2 hv
      exact ⟨q, hq, fun w hw => List.mem_cons_of_mem _ (hsub w hw)⟩

theorem exists_simple {a b : V} (p : DirectedWalk R a b) :
    ∃ q : DirectedWalk R a b, q.IsSimple ∧ ∀ w ∈ q.support, w ∈ p.support := by
  classical
  induction p with
  | nil a => exact ⟨.nil a, by simp [IsSimple, support], fun _ h => h⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq, hsub⟩ := ih
    by_cases ha : a ∈ q.support
    · obtain ⟨q', hq', hsub'⟩ := q.simple_suffix hq a ha
      exact ⟨q', hq', fun w hw => List.mem_cons_of_mem _ (hsub w (hsub' w hw))⟩
    · refine ⟨.cons hab q, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨ha, hq⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)

def Reachable (R : V → V → Prop) (a b : V) : Prop := Nonempty (DirectedWalk R a b)

theorem reachable_refl (R : V → V → Prop) (a : V) : Reachable R a a := ⟨.nil a⟩

theorem Reachable.step {a b c : V} (h : Reachable R a b) (hbc : R b c) :
    Reachable R a c := by
  obtain ⟨p⟩ := h
  exact ⟨p.append (.cons hbc (.nil c))⟩

end DirectedWalk

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FlowDelta -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [DecidableEq V]

def arcDelta (a b u v : V) : ℤ :=
  (if u = a ∧ v = b then 1 else 0) - (if u = b ∧ v = a then 1 else 0)

theorem arcDelta_skew (a b u v : V) : arcDelta a b u v = -arcDelta a b v u := by
  unfold arcDelta
  simp only [and_comm]
  ring

theorem arcDelta_sum [Fintype V] (a b u : V) :
    ∑ v, arcDelta a b u v = (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  simp [arcDelta, Finset.sum_sub_distrib, ite_and]

namespace DirectedWalk

variable {R : V → V → Prop}

def delta : {a b : V} → DirectedWalk R a b → V → V → ℤ
  | _, _, .nil _, _, _ => 0
  | a, _, .cons (b := b) _ p, u, v => arcDelta a b u v + p.delta u v

theorem delta_skew {a b : V} (p : DirectedWalk R a b) (u v : V) :
    p.delta u v = -p.delta v u := by
  induction p with
  | nil => simp [delta]
  | cons h p ih =>
    simp only [delta]
    rw [arcDelta_skew, ih]
    ring

theorem delta_sum [Fintype V] {a b : V} (p : DirectedWalk R a b) (u : V) :
    ∑ v, p.delta u v = (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  induction p with
  | nil => simp [delta]
  | cons h p ih =>
    simp only [delta, Finset.sum_add_distrib, arcDelta_sum, ih]
    ring

theorem delta_zero_of_not_mem {a b : V} (p : DirectedWalk R a b) (u v : V)
    (hu : u ∉ p.support) : p.delta u v = 0 := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    have hs : u ≠ a ∧ u ∉ p.support := by simpa [support] using hu
    have hb : u ≠ b := fun he => hs.2 (he.symm ▸ p.start_mem)
    simp [delta, arcDelta, hs.1, hb, ih hs.2]

theorem delta_bound [DecidableRel R] {a b : V} (p : DirectedWalk R a b) (hp : p.IsSimple)
    (u v : V) : p.delta u v ≤ if R u v then (1 : ℤ) else 0 := by
  classical
  induction p with
  | nil => simp only [delta]; split_ifs <;> norm_num
  | @cons a b c hab p ih =>
    have hs : a ∉ p.support ∧ p.IsSimple := by simpa [IsSimple, support] using hp
    have hab' : a ≠ b := fun he => hs.1 (he.symm ▸ p.start_mem)
    by_cases hu : u = a
    · subst u
      have hz := p.delta_zero_of_not_mem a v hs.1
      by_cases hv : v = b
      · subst v
        simp [delta, arcDelta, hz, hab', hab]
      · simp only [delta, hz, arcDelta, true_and, hv, hab', false_and,
          if_false, sub_self, add_zero]
        split_ifs <;> norm_num
    · by_cases hv : v = a
      · subst v
        have hz : p.delta u a = 0 := by rw [p.delta_skew, p.delta_zero_of_not_mem a u hs.1]; simp
        simp only [delta, hz, arcDelta, hu, false_and, and_true, if_false, zero_sub, add_zero]
        split_ifs <;> norm_num
      · have hz : arcDelta a b u v = 0 := by simp [arcDelta, hu, hv]
        simpa only [delta, hz, zero_add] using ih hs.2

end DirectedWalk

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: IntegerFlow -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [Fintype V]

structure IntegerFlow (cap : V → V → ℕ) (s t : V) where
  flow : V → V → ℤ
  skew : ∀ u v, flow u v = -flow v u
  capacity : ∀ u v, flow u v ≤ cap u v
  conservation : ∀ u, u ≠ s → u ≠ t → ∑ v, flow u v = 0

namespace IntegerFlow

variable {cap : V → V → ℕ} {s t : V}

def value (f : IntegerFlow cap s t) : ℤ := ∑ v, f.flow s v

def zero (cap : V → V → ℕ) (s t : V) : IntegerFlow cap s t where
  flow := fun _ _ => 0
  skew := by simp
  capacity := by intro u v; positivity
  conservation := by simp

theorem value_upper (f : IntegerFlow cap s t) : f.value ≤ ∑ v, (cap s v : ℤ) :=
  Finset.sum_le_sum (fun v _ => f.capacity s v)

theorem exists_maximum (cap : V → V → ℕ) (s t : V) :
    ∃ f : IntegerFlow cap s t, ∀ g : IntegerFlow cap s t, g.value ≤ f.value := by
  obtain ⟨z, ⟨f, hf⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ f : IntegerFlow cap s t, f.value = z)
    ⟨∑ v, (cap s v : ℤ), by rintro z ⟨f, rfl⟩; exact f.value_upper⟩
    ⟨(zero cap s t).value, zero cap s t, rfl⟩
  refine ⟨f, ?_⟩
  intro g
  rw [hf]
  exact hmax g.value ⟨g, rfl⟩

def Residual (f : IntegerFlow cap s t) (u v : V) : Prop := f.flow u v < cap u v

variable [DecidableEq V]

noncomputable def augment (f : IntegerFlow cap s t)
    (p : DirectedWalk f.Residual s t) (hp : p.IsSimple) : IntegerFlow cap s t where
  flow u v := f.flow u v + p.delta u v
  skew u v := by rw [f.skew, p.delta_skew]; ring
  capacity u v := by
    classical
    have hd := p.delta_bound hp u v
    by_cases h : f.Residual u v
    · simp only [if_pos h] at hd
      change f.flow u v < (cap u v : ℤ) at h
      omega
    · simp only [if_neg h] at hd
      have hc := f.capacity u v
      omega
  conservation u hus hut := by
    rw [Finset.sum_add_distrib, f.conservation u hus hut, p.delta_sum]
    simp [hus, hut]

theorem augment_value (f : IntegerFlow cap s t) (hst : s ≠ t)
    (p : DirectedWalk f.Residual s t) (hp : p.IsSimple) :
    (f.augment p hp).value = f.value + 1 := by
  simp [value, augment, Finset.sum_add_distrib, p.delta_sum, hst]

theorem maximum_no_residual_path (f : IntegerFlow cap s t) (hst : s ≠ t)
    (hmax : ∀ g : IntegerFlow cap s t, g.value ≤ f.value) :
    ¬ DirectedWalk.Reachable f.Residual s t := by
  rintro ⟨p⟩
  obtain ⟨q, hq, _⟩ := p.exists_simple
  have h := hmax (f.augment q hq)
  rw [f.augment_value hst q hq] at h
  omega

end IntegerFlow

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FlowCut -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

def cutCapacity (cap : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, cap u v

namespace IntegerFlow

variable {cap : V → V → ℕ} {s t : V}

omit [DecidableEq V] in
theorem internal_sum_zero (f : IntegerFlow cap s t) (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, f.flow u v = 0 := by
  have h : (∑ u ∈ S, ∑ v ∈ S, f.flow u v) =
      -(∑ u ∈ S, ∑ v ∈ S, f.flow u v) := by
    calc
      _ = ∑ v ∈ S, ∑ u ∈ S, f.flow u v := Finset.sum_comm
      _ = ∑ v ∈ S, ∑ u ∈ S, -f.flow v u := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        exact f.skew u v
      _ = _ := by simp only [Finset.sum_neg_distrib]
  omega

theorem cut_flow (f : IntegerFlow cap s t) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S) :
    f.value = ∑ u ∈ S, ∑ v ∈ Sᶜ, f.flow u v := by
  have hsum : ∑ u ∈ S, ∑ v, f.flow u v = f.value := by
    apply Finset.sum_eq_single s
    · intro u hu hus
      exact f.conservation u hus (fun h => ht (h ▸ hu))
    · exact fun h => False.elim (h hs)
  have hsplit : (∑ u ∈ S, ∑ v, f.flow u v) =
      (∑ u ∈ S, ∑ v ∈ S, f.flow u v) + ∑ u ∈ S, ∑ v ∈ Sᶜ, f.flow u v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl S (f.flow u)).symm
  rw [hsum, f.internal_sum_zero S, zero_add] at hsplit
  exact hsplit

theorem exists_flow_cut (cap : V → V → ℕ) (s t : V) (hst : s ≠ t) :
    ∃ (f : IntegerFlow cap s t) (S : Finset V),
      s ∈ S ∧ t ∉ S ∧ f.value = cutCapacity cap S := by
  classical
  obtain ⟨f, hmax⟩ := exists_maximum cap s t
  let S := Finset.univ.filter (fun v => DirectedWalk.Reachable f.Residual s v)
  have hs : s ∈ S := by simp [S, DirectedWalk.reachable_refl]
  have ht : t ∉ S := by
    simpa [S] using f.maximum_no_residual_path hst hmax
  refine ⟨f, S, hs, ht, ?_⟩
  rw [f.cut_flow S hs ht]
  simp only [cutCapacity, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hnot : ¬ f.Residual u v := by
    intro h
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := hu'.step h
    have hvm : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩
    exact (Finset.mem_compl.mp hv) hvm
  exact le_antisymm (f.capacity u v) (not_lt.mp hnot)

theorem exists_flow_of_cut_bound (cap : V → V → ℕ) (s t : V) (hst : s ≠ t)
    (k : ℕ) (hcut : ∀ S : Finset V, s ∈ S → t ∉ S → k ≤ cutCapacity cap S) :
    ∃ f : IntegerFlow cap s t, (k : ℤ) ≤ f.value := by
  obtain ⟨f, S, hs, ht, he⟩ := exists_flow_cut cap s t hst
  refine ⟨f, ?_⟩
  rw [he]
  exact_mod_cast hcut S hs ht

end IntegerFlow

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FlowPaths -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [DecidableEq V]

namespace DirectedWalk

variable {R : V → V → Prop}

def arcs : {a b : V} → DirectedWalk R a b → List (V × V)
  | _, _, .nil _ => []
  | a, _, .cons (b := b) _ p => (a, b) :: p.arcs

def Uses {a b : V} (p : DirectedWalk R a b) (u v : V) : Prop := (u, v) ∈ p.arcs

omit [DecidableEq V] in
theorem uses_ends {a b : V} (p : DirectedWalk R a b) {u v : V} (h : p.Uses u v) :
    u ∈ p.support ∧ v ∈ p.support := by
  induction p with
  | nil => simp [Uses, arcs] at h
  | @cons a b c hab p ih =>
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ p.start_mem⟩
    · obtain ⟨hu, hv⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv⟩

omit [DecidableEq V] in
theorem uses_rel {a b : V} (p : DirectedWalk R a b) {u v : V} (h : p.Uses u v) : R u v := by
  induction p with
  | nil => simp [Uses, arcs] at h
  | cons hab p ih =>
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hab
    · exact ih h

omit [DecidableEq V] in
theorem outgoing_of_mem {a b : V} (p : DirectedWalk R a b) {u : V}
    (hu : u ∈ p.support) (hub : u ≠ b) : ∃ v, p.Uses u v := by
  induction p with
  | nil a => exact False.elim (hub (by simpa [support] using hu))
  | @cons a b c hab p ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨b, List.mem_cons_self⟩
    · obtain ⟨v, hv⟩ := ih hu hub
      exact ⟨v, List.mem_cons_of_mem _ hv⟩

theorem delta_of_uses {a b : V} (p : DirectedWalk R a b) (hp : p.IsSimple)
    {u v : V} (h : p.Uses u v) : p.delta u v = 1 := by
  induction p with
  | nil => simp [Uses, arcs] at h
  | @cons a b c hab p ih =>
    have hs : a ∉ p.support ∧ p.IsSimple := by simpa [IsSimple, support] using hp
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨hu, hv⟩ := Prod.mk.inj he
      subst u
      subst v
      have hne : a ≠ b := fun he => hs.1 (he.symm ▸ p.start_mem)
      simp [delta, arcDelta, hne, p.delta_zero_of_not_mem a b hs.1]
    · obtain ⟨hu, hv⟩ := p.uses_ends h
      have hua : u ≠ a := fun he => hs.1 (he ▸ hu)
      have hva : v ≠ a := fun he => hs.1 (he ▸ hv)
      simpa [delta, arcDelta, hua, hva] using ih hs.2 h

end DirectedWalk

namespace IntegerFlow

variable [Fintype V] {cap : V → V → ℕ} {s t : V}

def Positive (f : IntegerFlow cap s t) (u v : V) : Prop := 0 < f.flow u v

theorem exists_positive_path (f : IntegerFlow cap s t) (hf : 0 < f.value) :
    ∃ p : DirectedWalk f.Positive s t, p.IsSimple := by
  classical
  have hr : DirectedWalk.Reachable f.Positive s t := by
    by_contra ht
    let S := Finset.univ.filter (fun v => DirectedWalk.Reachable f.Positive s v)
    have hs : s ∈ S := by simp [S, DirectedWalk.reachable_refl]
    have htS : t ∉ S := by simpa [S] using ht
    have heq := f.cut_flow S hs htS
    have hn : (∑ u ∈ S, ∑ v ∈ Sᶜ, f.flow u v) ≤ 0 := by
      apply Finset.sum_nonpos
      intro u hu
      apply Finset.sum_nonpos
      intro v hv
      apply le_of_not_gt
      intro huv
      have hu' := (Finset.mem_filter.mp hu).2
      have hv' := hu'.step huv
      exact (Finset.mem_compl.mp hv) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩)
    omega
  obtain ⟨p⟩ := hr
  obtain ⟨q, hq, _⟩ := p.exists_simple
  exact ⟨q, hq⟩

noncomputable def decrement (f : IntegerFlow cap s t)
    (p : DirectedWalk f.Positive s t) (hp : p.IsSimple) : IntegerFlow cap s t where
  flow u v := f.flow u v - p.delta u v
  skew u v := by rw [f.skew, p.delta_skew]; ring
  capacity u v := by
    classical
    have hd := p.delta_bound hp v u
    rw [p.delta_skew v u] at hd
    by_cases h : f.Positive v u
    · simp only [if_pos h] at hd
      change 0 < f.flow v u at h
      have hs := f.skew u v
      have hc : (0 : ℤ) ≤ cap u v := by positivity
      omega
    · simp only [if_neg h] at hd
      have hc := f.capacity u v
      omega
  conservation u hus hut := by
    rw [Finset.sum_sub_distrib, f.conservation u hus hut, p.delta_sum]
    simp [hus, hut]

theorem decrement_value (f : IntegerFlow cap s t) (hst : s ≠ t)
    (p : DirectedWalk f.Positive s t) (hp : p.IsSimple) :
    (f.decrement p hp).value = f.value - 1 := by
  simp [value, decrement, Finset.sum_sub_distrib, p.delta_sum, hst]

theorem decrement_used (f : IntegerFlow cap s t)
    (p : DirectedWalk f.Positive s t) (hp : p.IsSimple)
    {u v : V} (h : p.Uses u v) :
    (f.decrement p hp).flow u v = f.flow u v - 1 := by
  simp only [decrement, p.delta_of_uses hp h]

end IntegerFlow

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FanNetwork -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

abbrev FanNode (V : Type*) := (Fin 2) ⊕ (V × Bool)

namespace FanNetwork

variable {V : Type*} [DecidableEq V]

def source : FanNode V := Sum.inl 0
def sink : FanNode V := Sum.inl 1
def input (v : V) : FanNode V := Sum.inr (v, false)
def output (v : V) : FanNode V := Sum.inr (v, true)

omit [DecidableEq V] in
theorem source_ne_sink : (source : FanNode V) ≠ sink := by simp [source, sink]

omit [DecidableEq V] in
theorem input_injective : Function.Injective (input : V → FanNode V) := by
  intro u v h
  exact congrArg Prod.fst (Sum.inr.inj h)

def capacity (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V) :
    FanNode V → FanNode V → ℕ
  | .inl i, .inr (v, false) => if i = 0 ∧ G.Adj a v then 3 else 0
  | .inr (u, false), .inr (v, true) => if u = v ∧ u ≠ a then 1 else 0
  | .inr (u, true), .inr (v, false) => if u ∉ T ∧ v ≠ a ∧ G.Adj u v then 3 else 0
  | .inr (u, true), .inl j => if j = 1 ∧ u ∈ T then 3 else 0
  | _, _ => 0

theorem capacity_source (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    {v : V} (h : G.Adj a v) : capacity G a T source (input v) = 3 := by
  simp [capacity, source, input, h]

theorem capacity_split (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    {v : V} (h : v ≠ a) : capacity G a T (input v) (output v) = 1 := by
  simp [capacity, input, output, h]

theorem capacity_target (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    {v : V} (h : v ∈ T) : capacity G a T (output v) sink = 3 := by
  simp [capacity, output, sink, h]

theorem capacity_edge (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    {u v : V} (hu : u ∉ T) (hv : v ≠ a) (h : G.Adj u v) :
    capacity G a T (output u) (input v) = 3 := by
  simp [capacity, output, input, hu, hv, h]

end FanNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem capacity_le_cut (cap : V → V → ℕ) (S : Finset V) {u v : V}
    (hu : u ∈ S) (hv : v ∉ S) : cap u v ≤ cutCapacity cap S := by
  change cap u v ≤ ∑ z ∈ S, ∑ w ∈ Sᶜ, cap z w
  have h1 : cap u v ≤ ∑ w ∈ Sᶜ, cap u w :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_compl.mpr hv)
  have h2 := Finset.single_le_sum (f := fun z => ∑ w ∈ Sᶜ, cap z w)
    (fun _ _ => Nat.zero_le _) hu
  exact h1.trans h2

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FanCut -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every deletion of at most two vertices still permits a root-to-target path. -/
def ThreeFanCondition (G : SimpleGraph V) (a : V) (T : Finset V) : Prop :=
  a ∉ T ∧ ∀ Z : Finset V, Z.card ≤ 2 → a ∉ Z →
    ∃ b ∈ T, ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ Z

namespace FanNetwork

theorem split_cut_card (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    (S : Finset (FanNode V)) :
    (Finset.univ.filter (fun v => v ≠ a ∧ input v ∈ S ∧ output v ∉ S)).card ≤
      cutCapacity (capacity G a T) S := by
  let Z := Finset.univ.filter (fun v => v ≠ a ∧ input v ∈ S ∧ output v ∉ S)
  have hsub : Z.image input ⊆ S := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hv).2.2.1
  calc
    Z.card = ∑ _v ∈ Z, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ Z, ∑ w ∈ Sᶜ, capacity G a T (input v) w := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨ha, _, ho⟩ := (Finset.mem_filter.mp hv).2
      rw [← capacity_split G a T ha]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_compl.mpr ho)
    _ = ∑ u ∈ Z.image input, ∑ w ∈ Sᶜ, capacity G a T u w := by
      symm
      exact Finset.sum_image (fun u _ v _ h => input_injective h)
    _ ≤ cutCapacity (capacity G a T) S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro _ _ _
      exact Nat.zero_le _

theorem cut_bound (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    (hfan : ThreeFanCondition G a T) (S : Finset (FanNode V))
    (hs : source ∈ S) (ht : sink ∉ S) : 3 ≤ cutCapacity (capacity G a T) S := by
  by_contra hcut
  have hsmall : cutCapacity (capacity G a T) S ≤ 2 := by omega
  let Z := Finset.univ.filter (fun v => v ≠ a ∧ input v ∈ S ∧ output v ∉ S)
  have hZ : Z.card ≤ 2 := (split_cut_card G a T S).trans hsmall
  have haZ : a ∉ Z := by simp [Z]
  have hlarge : ∀ u ∈ S, ∀ v, 3 ≤ capacity G a T u v → v ∈ S := by
    intro u hu v hcap
    by_contra hv
    have h := capacity_le_cut (capacity G a T) S hu hv
    omega
  have htarget : ∀ v, output v ∈ S → v ∉ T := by
    intro v hv hT
    apply ht
    exact hlarge _ hv _ (by rw [capacity_target G a T hT])
  have hsplit : ∀ v, v ≠ a → v ∉ Z → input v ∈ S → output v ∈ S := by
    intro v hva hvZ hin
    by_contra hout
    exact hvZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hva, hin, hout⟩)
  have hstep : ∀ u v, G.Adj u v → v ∉ Z →
      (u = a ∨ output u ∈ S) → (v = a ∨ output v ∈ S) := by
    intro u v huv hvZ hu
    by_cases hva : v = a
    · exact Or.inl hva
    · apply Or.inr
      apply hsplit v hva hvZ
      rcases hu with he | hu
      · subst u
        exact hlarge _ hs _ (by rw [capacity_source G a T huv])
      · exact hlarge _ hu _ (by rw [capacity_edge G a T (htarget u hu) hva huv])
  have hwalk : ∀ {u v : V} (p : G.Walk u v), (∀ w ∈ p.support, w ∉ Z) →
      (u = a ∨ output u ∈ S) → (v = a ∨ output v ∈ S) := by
    intro u v p
    induction p with
    | nil => intro _ hu; exact hu
    | @cons u v w huv p ih =>
      intro hav hu
      apply ih
      · intro z hz
        exact hav z (List.mem_cons_of_mem _ hz)
      · exact hstep u v huv (hav v (List.mem_cons_of_mem _ p.start_mem_support)) hu
  obtain ⟨b, hb, p, hp⟩ := hfan.2 Z hZ haZ
  rcases hwalk p hp (Or.inl rfl) with he | he
  · exact hfan.1 (he ▸ hb)
  · exact htarget b he hb

theorem exists_three_flow (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    (hfan : ThreeFanCondition G a T) :
    ∃ f : IntegerFlow (capacity G a T) source sink, 3 ≤ f.value :=
  IntegerFlow.exists_flow_of_cut_bound (capacity G a T) source sink source_ne_sink 3
    (cut_bound G a T hfan)

end FanNetwork

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FanArcs -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof.FanNetwork

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)

@[simp] private theorem positive_if_three (P : Prop) [Decidable P] :
    (0 : ℕ) < (if P then 3 else 0) ↔ P := by
  by_cases h : P <;> simp [h]

@[simp] private theorem positive_if_one (P : Prop) [Decidable P] :
    (0 : ℕ) < (if P then 1 else 0) ↔ P := by
  by_cases h : P <;> simp [h]

theorem positive_from_source (q : FanNode V) :
    0 < capacity G a T source q ↔ ∃ v, q = input v ∧ G.Adj a v := by
  cases q with
  | inl i => fin_cases i <;> simp [source, input, capacity]
  | inr z => rcases z with ⟨v, b⟩; cases b <;> simp [source, input, capacity]

theorem positive_from_input (v : V) (q : FanNode V) :
    0 < capacity G a T (input v) q ↔ q = output v ∧ v ≠ a := by
  cases q with
  | inl i => fin_cases i <;> simp [input, output, capacity]
  | inr z => rcases z with ⟨u, b⟩; cases b <;> simp [input, output, capacity, eq_comm]

theorem positive_into_output (v : V) (q : FanNode V) :
    0 < capacity G a T q (output v) ↔ q = input v ∧ v ≠ a := by
  cases q with
  | inl i => fin_cases i <;> simp [input, output, capacity]
  | inr z =>
    rcases z with ⟨u, b⟩
    cases b
    · by_cases h : u = v
      · subst u
        by_cases h : v = a <;> simp [input, output, capacity, h]
      · simp [input, output, capacity, h]
    · simp [input, output, capacity]

theorem positive_into_sink (q : FanNode V) :
    0 < capacity G a T q sink ↔ ∃ v, q = output v ∧ v ∈ T := by
  cases q with
  | inl i => fin_cases i <;> simp [sink, output, capacity]
  | inr z => rcases z with ⟨v, b⟩; cases b <;> simp [sink, output, capacity]

theorem positive_from_output (u : V) (q : FanNode V) :
    0 < capacity G a T (output u) q ↔
      (q = sink ∧ u ∈ T) ∨ ∃ v, q = input v ∧ u ∉ T ∧ v ≠ a ∧ G.Adj u v := by
  cases q with
  | inl i => fin_cases i <;> simp [sink, output, input, capacity]
  | inr z => rcases z with ⟨v, b⟩; cases b <;> simp [sink, output, input, capacity]

theorem sink_capacity_zero (q : FanNode V) : capacity G a T sink q = 0 := by
  cases q with
  | inl i => fin_cases i <;> simp [sink, capacity]
  | inr z => rcases z with ⟨v, b⟩; cases b <;> simp [sink, capacity]

def nodeValue (a : V) : FanNode V → V := Sum.elim (fun _ => a) Prod.fst

theorem positive_projects (q z : FanNode V) (hz : z ≠ sink)
    (h : 0 < capacity G a T q z) :
    nodeValue a q = nodeValue a z ∨ G.Adj (nodeValue a q) (nodeValue a z) := by
  cases q with
  | inl i =>
    fin_cases i
    · obtain ⟨v, rfl, hv⟩ := (positive_from_source G a T z).mp h
      exact Or.inr hv
    · change 0 < capacity G a T sink z at h
      rw [sink_capacity_zero G a T z] at h
      omega
  | inr q =>
    rcases q with ⟨u, b⟩
    cases b
    · obtain ⟨rfl, _⟩ := (positive_from_input G a T u z).mp h
      exact Or.inl rfl
    · rcases (positive_from_output G a T u z).mp h with ⟨he, _⟩ | ⟨v, rfl, _, _, huv⟩
      · exact False.elim (hz he)
      · exact Or.inr huv

end ChvatalPolytopes.SeriesParallel.Proof.FanNetwork

end

/- Complete checked body: DirectedGraphPath -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof.DirectedWalk

variable {V W : Type*} {R : V → V → Prop}

theorem incoming_of_mem {a b : V} (p : DirectedWalk R a b) {v : V}
    (hv : v ∈ p.support) (hva : v ≠ a) : ∃ u, p.Uses u v := by
  induction p with
  | nil a => exact False.elim (hva (by simpa [support] using hv))
  | @cons a b c hab p ih =>
    have hvp : v ∈ p.support := (List.mem_cons.mp hv).resolve_left hva
    by_cases hvb : v = b
    · subst v
      exact ⟨a, List.mem_cons_self⟩
    · obtain ⟨u, hu⟩ := ih hvp hvb
      exact ⟨u, List.mem_cons_of_mem _ hu⟩

theorem last_arc {a b : V} (p : DirectedWalk R a b) (hp : p.IsSimple) (hab : a ≠ b) :
    ∃ u, ∃ q : DirectedWalk R a u, R u b ∧ q.IsSimple ∧ b ∉ q.support ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧ (∀ v w, q.Uses v w → p.Uses v w) := by
  induction p with
  | nil a => exact False.elim (hab rfl)
  | @cons a b c h p ih =>
    have hs : a ∉ p.support ∧ p.IsSimple := by simpa [IsSimple, support] using hp
    by_cases hbc : b = c
    · subst c
      refine ⟨a, .nil a, h, ?_, ?_, ?_, ?_⟩
      · simp [IsSimple, support]
      · simpa [support] using hab.symm
      · intro v hv
        have he : v = a := by simpa [support] using hv
        subst v
        exact List.mem_cons_self
      · intro v w hv
        simp [Uses, arcs] at hv
    · obtain ⟨u, q, hlast, hq, hc, hsub, harcs⟩ := ih hs.2 hbc
      refine ⟨u, .cons h q, hlast, ?_, ?_, ?_, ?_⟩
      · apply List.nodup_cons.mpr
        exact ⟨fun ha => hs.1 (hsub a ha), hq⟩
      · simpa [support] using And.intro hab.symm hc
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub v hv)
      · intro v w hv
        rcases List.mem_cons.mp hv with he | hv
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons_of_mem _ (harcs v w hv)

theorem project_walk (G : SimpleGraph W) (f : V → W) {a b : V}
    (p : DirectedWalk R a b)
    (h : ∀ u v, p.Uses u v → f u = f v ∨ G.Adj (f u) (f v)) :
    ∃ q : G.Walk (f a) (f b), ∀ w ∈ q.support, ∃ v ∈ p.support, f v = w := by
  induction p with
  | nil a =>
    refine ⟨.nil, ?_⟩
    intro w hw
    have he : w = f a := by simpa using hw
    exact ⟨a, by simp [support], he.symm⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq⟩ := ih (fun u v huv => h u v (List.mem_cons_of_mem _ huv))
    rcases h a b List.mem_cons_self with he | he
    · refine ⟨q.copy he.symm rfl, ?_⟩
      intro w hw
      obtain ⟨v, hv, hf⟩ := hq w (by simpa using hw)
      exact ⟨v, List.mem_cons_of_mem _ hv, hf⟩
    · refine ⟨.cons he q, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨a, List.mem_cons_self, rfl⟩
      · obtain ⟨v, hv, hf⟩ := hq w hw
        exact ⟨v, List.mem_cons_of_mem _ hv, hf⟩

end ChvatalPolytopes.SeriesParallel.Proof.DirectedWalk

end

/- Complete checked body: FanDecode -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof.FanNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)

theorem flow_positive_capacity (f : IntegerFlow (capacity G a T) source sink)
    {u v : FanNode V} (h : f.Positive u v) : 0 < capacity G a T u v := by
  have hc := f.capacity u v
  change 0 < f.flow u v at h
  exact_mod_cast h.trans_le hc

theorem input_used (f : IntegerFlow (capacity G a T) source sink)
    (p : DirectedWalk f.Positive source sink) (v : V) (hv : input v ∈ p.support) :
    p.Uses (input v) (output v) := by
  obtain ⟨q, hq⟩ := p.outgoing_of_mem hv (by simp [input, sink])
  have hc := flow_positive_capacity G a T f (p.uses_rel hq)
  obtain ⟨he, _⟩ := (positive_from_input G a T v q).mp hc
  simpa only [he] using hq

theorem output_used (f : IntegerFlow (capacity G a T) source sink)
    (p : DirectedWalk f.Positive source sink) (v : V) (hv : output v ∈ p.support) :
    p.Uses (input v) (output v) := by
  obtain ⟨q, hq⟩ := p.incoming_of_mem hv (by simp [output, source])
  have hc := flow_positive_capacity G a T f (p.uses_rel hq)
  obtain ⟨he, _⟩ := (positive_into_output G a T v q).mp hc
  simpa only [he] using hq

theorem projected_used (f : IntegerFlow (capacity G a T) source sink)
    (p : DirectedWalk f.Positive source sink) {q : FanNode V} (hq : q ∈ p.support)
    {v : V} (hval : nodeValue a q = v) (hv : v ≠ a) :
    p.Uses (input v) (output v) := by
  cases q with
  | inl i => exact False.elim (hv hval.symm)
  | inr q =>
    rcases q with ⟨u, b⟩
    change u = v at hval
    subst u
    cases b
    · exact input_used G a T f p v hq
    · exact output_used G a T f p v hq

theorem decode_path (haT : a ∉ T) (f : IntegerFlow (capacity G a T) source sink)
    (p : DirectedWalk f.Positive source sink) (hp : p.IsSimple) :
    ∃ b ∈ T, ∃ q : G.Walk a b, q.IsPath ∧
      (∀ v ∈ q.support, v ∈ T → v = b) ∧
      (∀ v ∈ q.support, v ≠ a → p.Uses (input v) (output v)) := by
  classical
  obtain ⟨z, pre, hlast, _hprefix, hsink, hsub, _harcs⟩ :=
    p.last_arc hp source_ne_sink
  have hcap := flow_positive_capacity G a T f hlast
  obtain ⟨b, rfl, hb⟩ := (positive_into_sink G a T z).mp hcap
  have hmap : ∀ u v, pre.Uses u v →
      nodeValue a u = nodeValue a v ∨ G.Adj (nodeValue a u) (nodeValue a v) := by
    intro u v huv
    have hv : v ≠ sink := fun he => hsink (he ▸ (pre.uses_ends huv).2)
    exact positive_projects G a T u v hv
      (flow_positive_capacity G a T f (pre.uses_rel huv))
  obtain ⟨q, hq⟩ := pre.project_walk G (nodeValue a) hmap
  change ∃ b ∈ T, ∃ q : G.Walk a b, q.IsPath ∧
    (∀ v ∈ q.support, v ∈ T → v = b) ∧
    (∀ v ∈ q.support, v ≠ a → p.Uses (input v) (output v))
  refine ⟨b, hb, q.bypass, q.bypass_isPath, ?_, ?_⟩
  · intro v hv hvT
    obtain ⟨w, hw, hwv⟩ := hq v (q.support_bypass_subset_support hv)
    have hout : output v ∈ pre.support := by
      cases w with
      | inl i =>
        have he : a = v := hwv
        exact False.elim (haT (he.symm ▸ hvT))
      | inr w =>
        rcases w with ⟨u, flag⟩
        change u = v at hwv
        subst u
        cases flag
        · obtain ⟨n, hn⟩ := pre.outgoing_of_mem hw (by simp [output])
          have hc := flow_positive_capacity G a T f (pre.uses_rel hn)
          have he := ((positive_from_input G a T v n).mp hc).1
          exact he ▸ (pre.uses_ends hn).2
        · exact hw
    by_contra hne
    have ho : output v ≠ output b := by
      intro h
      exact hne (congrArg Prod.fst (Sum.inr.inj h))
    obtain ⟨w, hw⟩ := pre.outgoing_of_mem hout ho
    have hc := flow_positive_capacity G a T f (pre.uses_rel hw)
    rcases (positive_from_output G a T v w).mp hc with ⟨he, _⟩ | ⟨_, _, hn, _⟩
    · exact hsink (he ▸ (pre.uses_ends hw).2)
    · exact hn hvT
  · intro v hv hva
    obtain ⟨w, hw, hwv⟩ := hq v (q.support_bypass_subset_support hv)
    exact projected_used G a T f p (hsub w hw) hwv hva

end ChvatalPolytopes.SeriesParallel.Proof.FanNetwork

end

/- Complete checked body: FlowSeparation -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof.IntegerFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {cap : V → V → ℕ} {s t : V}

theorem decrement_positive (f : IntegerFlow cap s t)
    (p : DirectedWalk f.Positive s t) (hp : p.IsSimple) {u v : V}
    (h : 0 < (f.decrement p hp).flow u v) : 0 < f.flow u v := by
  classical
  by_contra hn
  have hf : f.flow u v ≤ 0 := le_of_not_gt hn
  have hd := p.delta_bound hp v u
  rw [p.delta_skew v u] at hd
  change 0 < f.flow u v - p.delta u v at h
  have hs := f.skew u v
  by_cases hr : f.Positive v u
  · simp only [if_pos hr] at hd
    change 0 < f.flow v u at hr
    omega
  · simp only [if_neg hr] at hd
    omega

theorem used_unit_nonpositive (f : IntegerFlow cap s t)
    (p : DirectedWalk f.Positive s t) (hp : p.IsSimple) {u v : V}
    (hcap : cap u v ≤ 1) (huse : p.Uses u v) :
    (f.decrement p hp).flow u v ≤ 0 := by
  rw [f.decrement_used p hp huse]
  have hc := f.capacity u v
  have hc' : (cap u v : ℤ) ≤ 1 := by exact_mod_cast hcap
  omega

end ChvatalPolytopes.SeriesParallel.Proof.IntegerFlow

end

/- Complete checked body: ThreeFan -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

structure ThreeFan {V : Type*} (G : SimpleGraph V) (a : V) (T : Finset V) where
  endpoint : Fin 3 → V
  distinct : Function.Injective endpoint
  target : ∀ i, endpoint i ∈ T
  path : ∀ i, G.Walk a (endpoint i)
  simple : ∀ i, (path i).IsPath
  target_only : ∀ i v, v ∈ (path i).support → v ∈ T → v = endpoint i
  intersect : ∀ i j, i ≠ j → ∀ v,
    v ∈ (path i).support → v ∈ (path j).support → v = a

theorem exists_three_fan {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (T : Finset V)
    (hfan : ThreeFanCondition G a T) : Nonempty (ThreeFan G a T) := by
  classical
  obtain ⟨f, hf⟩ := FanNetwork.exists_three_flow G a T hfan
  obtain ⟨p0, hp0⟩ := f.exists_positive_path (by omega)
  let f1 := f.decrement p0 hp0
  have hf1 : 2 ≤ f1.value := by rw [IntegerFlow.decrement_value _ FanNetwork.source_ne_sink]; omega
  obtain ⟨p1, hp1⟩ := f1.exists_positive_path (by omega)
  let f2 := f1.decrement p1 hp1
  have hf2 : 1 ≤ f2.value := by rw [IntegerFlow.decrement_value _ FanNetwork.source_ne_sink]; omega
  obtain ⟨p2, hp2⟩ := f2.exists_positive_path (by omega)
  obtain ⟨b0, hb0, q0, hq0, ht0, hu0⟩ := FanNetwork.decode_path G a T hfan.1 f p0 hp0
  obtain ⟨b1, hb1, q1, hq1, ht1, hu1⟩ := FanNetwork.decode_path G a T hfan.1 f1 p1 hp1
  obtain ⟨b2, hb2, q2, hq2, ht2, hu2⟩ := FanNetwork.decode_path G a T hfan.1 f2 p2 hp2
  have h01 : ∀ v, v ∈ q0.support → v ∈ q1.support → v = a := by
    intro v hv0 hv1
    by_contra hne
    have hcap : FanNetwork.capacity G a T (FanNetwork.input v) (FanNetwork.output v) ≤ 1 :=
      le_of_eq (FanNetwork.capacity_split G a T hne)
    have hn := f.used_unit_nonpositive p0 hp0 hcap (hu0 v hv0 hne)
    have hp := p1.uses_rel (hu1 v hv1 hne)
    exact (not_lt_of_ge hn) hp
  have h02 : ∀ v, v ∈ q0.support → v ∈ q2.support → v = a := by
    intro v hv0 hv2
    by_contra hne
    have hcap : FanNetwork.capacity G a T (FanNetwork.input v) (FanNetwork.output v) ≤ 1 :=
      le_of_eq (FanNetwork.capacity_split G a T hne)
    have hn := f.used_unit_nonpositive p0 hp0 hcap (hu0 v hv0 hne)
    have hp := f1.decrement_positive p1 hp1 (p2.uses_rel (hu2 v hv2 hne))
    exact (not_lt_of_ge hn) hp
  have h12 : ∀ v, v ∈ q1.support → v ∈ q2.support → v = a := by
    intro v hv1 hv2
    by_contra hne
    have hcap : FanNetwork.capacity G a T (FanNetwork.input v) (FanNetwork.output v) ≤ 1 :=
      le_of_eq (FanNetwork.capacity_split G a T hne)
    have hn := f1.used_unit_nonpositive p1 hp1 hcap (hu1 v hv1 hne)
    exact (not_lt_of_ge hn) (p2.uses_rel (hu2 v hv2 hne))
  let b : Fin 3 → V := Fin.cases b0 (Fin.cases b1 (fun _ => b2))
  let q : ∀ i : Fin 3, G.Walk a (b i) := Fin.cases q0 (Fin.cases q1 (fun _ => q2))
  have hb : ∀ i, b i ∈ T := by intro i; fin_cases i <;> assumption
  have hq : ∀ i, (q i).IsPath := by intro i; fin_cases i <;> assumption
  have ht : ∀ i v, v ∈ (q i).support → v ∈ T → v = b i := by
    intro i
    fin_cases i <;> assumption
  have hi : ∀ i j, i ≠ j → ∀ v, v ∈ (q i).support → v ∈ (q j).support → v = a := by
    intro i j hij v hv hv'
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | exact h01 v hv hv'
      | exact h01 v hv' hv
      | exact h02 v hv hv'
      | exact h02 v hv' hv
      | exact h12 v hv hv'
      | exact h12 v hv' hv
  refine ⟨⟨b, ?_, hb, q, hq, ht, hi⟩⟩
  intro i j hij
  by_contra hne
  have he : b i = a := hi i j hne (b i) (q i).end_mem_support
    (hij.symm ▸ (q j).end_mem_support)
  exact hfan.1 (he ▸ hb i)

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: SmallSeparators -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [DecidableEq V]

def AvoidReach (G : SimpleGraph V) (Z : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ Z

namespace AvoidReach

variable {G : SimpleGraph V} {Z : Finset V} {u v w : V}

omit [DecidableEq V] in
theorem refl (hu : u ∉ Z) : AvoidReach G Z u u :=
  ⟨.nil, by
    intro w hw
    have he : w = u := by simpa using hw
    simpa only [he] using hu⟩

omit [DecidableEq V] in
theorem symm (h : AvoidReach G Z u v) : AvoidReach G Z v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun w hw => hp w (by simpa using hw)⟩

omit [DecidableEq V] in
theorem trans (h : AvoidReach G Z u v) (h' : AvoidReach G Z v w) : AvoidReach G Z u w := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨p.append q, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact hp z hz
  · exact hq z hz

omit [DecidableEq V] in
theorem endpoints (h : AvoidReach G Z u v) : u ∉ Z ∧ v ∉ Z := by
  obtain ⟨p, hp⟩ := h
  exact ⟨hp u p.start_mem_support, hp v p.end_mem_support⟩

omit [DecidableEq V] in
theorem mono {Y : Finset V} (h : AvoidReach G Z u v) (hYZ : Y ⊆ Z) : AvoidReach G Y u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun w hw hy => hp w hw (hYZ hy)⟩

omit [DecidableEq V] in
theorem adj_step (h : AvoidReach G Z u v) (hvw : G.Adj v w) (hw : w ∉ Z) :
    AvoidReach G Z u w := by
  apply h.trans
  refine ⟨.cons hvw .nil, ?_⟩
  intro z hz
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact h.endpoints.2
  · exact hw

theorem support_reachable {p : G.Walk u v} (hp : ∀ w ∈ p.support, w ∉ Z)
    {w : V} (hw : w ∈ p.support) : AvoidReach G Z u w :=
  ⟨p.takeUntil w hw, fun z hz => hp z (p.support_takeUntil_subset_support hw hz)⟩

end AvoidReach

def NoSmallSeparator (G : SimpleGraph V) : Prop :=
  ∀ Z : Finset V, Z.card ≤ 2 → ∀ u v, u ∉ Z → v ∉ Z → AvoidReach G Z u v

theorem NoSmallSeparator.fan_condition [Fintype V] {G : SimpleGraph V}
    (hG : NoSmallSeparator G) (a : V) (T : Finset V) (hT : 3 ≤ T.card) (ha : a ∉ T) :
    ThreeFanCondition G a T := by
  refine ⟨ha, ?_⟩
  intro Z hZ haZ
  have hex : ∃ b ∈ T, b ∉ Z := by
    by_contra! h
    have hh : T.card ≤ Z.card := Finset.card_le_card h
    omega
  obtain ⟨b, hb, hbZ⟩ := hex
  obtain ⟨p, hp⟩ := hG Z hZ a b haZ hbZ
  exact ⟨b, hb, p, hp⟩

theorem exists_minimal_separator {G : SimpleGraph V} (hG : ¬ NoSmallSeparator G) :
    ∃ (Z : Finset V) (a b : V), Z.card ≤ 2 ∧ a ∉ Z ∧ b ∉ Z ∧
      ¬ AvoidReach G Z a b ∧
      ∀ z ∈ Z, AvoidReach G (Z.erase z) a b := by
  classical
  simp only [NoSmallSeparator, not_forall] at hG
  obtain ⟨Y, hY, a, b, ha, hb, hab⟩ := hG
  let F := Y.powerset.filter (fun Z => ¬ AvoidReach G Z a b)
  have hF : F.Nonempty := ⟨Y, by simp [F, hab]⟩
  obtain ⟨Z, hZF, hmin⟩ := Finset.exists_min_image F Finset.card hF
  obtain ⟨hZY, hsep⟩ : Z ⊆ Y ∧ ¬ AvoidReach G Z a b := by simpa [F] using hZF
  refine ⟨Z, a, b, (Finset.card_le_card hZY).trans hY,
    fun h => ha (hZY h), fun h => hb (hZY h), hsep, ?_⟩
  intro z hz
  by_contra h
  have he : Z.erase z ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset z Z).trans hZY, h⟩
  have hh := hmin (Z.erase z) he
  have hs := Finset.card_erase_lt_of_mem hz
  omega

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: SeparatorComponents -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def reachComponent (G : SimpleGraph V) (Z : Finset V) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => AvoidReach G Z a v)

omit [DecidableEq V] in
@[simp] theorem mem_reachComponent (G : SimpleGraph V) (Z : Finset V) (a v : V) :
    v ∈ reachComponent G Z a ↔ AvoidReach G Z a v := by
  classical
  simp [reachComponent]

omit [DecidableEq V] in
theorem reachComponent_nonempty (G : SimpleGraph V) (Z : Finset V) (a : V) (ha : a ∉ Z) :
    (reachComponent G Z a).Nonempty :=
  ⟨a, (mem_reachComponent G Z a a).mpr (AvoidReach.refl ha)⟩

omit [DecidableEq V] in
theorem reachComponent_outside (G : SimpleGraph V) (Z : Finset V) (a v : V)
    (hv : v ∈ reachComponent G Z a) : v ∉ Z :=
  ((mem_reachComponent G Z a v).mp hv).endpoints.2

omit [DecidableEq V] in
theorem reachComponent_adj (G : SimpleGraph V) (Z : Finset V) (a : V) {u v : V}
    (hu : u ∈ reachComponent G Z a) (huv : G.Adj u v) (hv : v ∉ Z) :
    v ∈ reachComponent G Z a :=
  (mem_reachComponent G Z a v).mpr (((mem_reachComponent G Z a u).mp hu).adj_step huv hv)

omit [DecidableEq V] in
theorem reachComponent_disjoint (G : SimpleGraph V) (Z : Finset V) (a b : V)
    (hab : ¬ AvoidReach G Z a b) :
    Disjoint (reachComponent G Z a) (reachComponent G Z b) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  apply hab
  exact ((mem_reachComponent G Z a v).mp hv).trans
    ((mem_reachComponent G Z b v).mp hv').symm

theorem reachComponent_neighbor_union (G : SimpleGraph V) (Z : Finset V) (a : V)
    {u v : V} (hu : u ∈ reachComponent G Z a) (huv : G.Adj u v) :
    v ∈ reachComponent G Z a ∪ Z := by
  by_cases hv : v ∈ Z
  · exact Finset.mem_union.mpr (Or.inr hv)
  · exact Finset.mem_union.mpr (Or.inl (reachComponent_adj G Z a hu huv hv))

structure MinimalSeparator (G : SimpleGraph V) where
  cut : Finset V
  small : cut.card ≤ 2
  left : V
  right : V
  left_outside : left ∉ cut
  right_outside : right ∉ cut
  separates : ¬ AvoidReach G cut left right
  minimal : ∀ z ∈ cut, AvoidReach G (cut.erase z) left right

omit [Fintype V] in
theorem exists_minimalSeparator (G : SimpleGraph V) (h : ¬ NoSmallSeparator G) :
    Nonempty (MinimalSeparator G) := by
  obtain ⟨Z, a, b, hZ, ha, hb, hab, hmin⟩ := exists_minimal_separator h
  exact ⟨⟨Z, hZ, a, b, ha, hb, hab, hmin⟩⟩

namespace MinimalSeparator

variable {G : SimpleGraph V}

def swap (D : MinimalSeparator G) : MinimalSeparator G where
  cut := D.cut
  small := D.small
  left := D.right
  right := D.left
  left_outside := D.right_outside
  right_outside := D.left_outside
  separates h := D.separates h.symm
  minimal z hz := (D.minimal z hz).symm

theorem right_not_union (D : MinimalSeparator G) :
    D.right ∉ reachComponent G D.cut D.left ∪ D.cut := by
  simp only [Finset.mem_union, not_or]
  exact ⟨fun h => D.separates ((mem_reachComponent _ _ _ _).mp h), D.right_outside⟩

theorem choose_clique_side (D : MinimalSeparator G) (K : Finset V)
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) :
    ∃ D' : MinimalSeparator G,
      ∀ v ∈ reachComponent G D'.cut D'.left, v ∉ K := by
  classical
  by_cases h : ∃ v ∈ reachComponent G D.cut D.left, v ∈ K
  · obtain ⟨v, hv, hvK⟩ := h
    refine ⟨D.swap, ?_⟩
    intro w hw hwK
    have hw' : w ∈ reachComponent G D.cut D.right := hw
    have hdis := reachComponent_disjoint G D.cut D.left D.right D.separates
    have hne : v ≠ w := fun he => Finset.disjoint_left.mp hdis (he ▸ hv) hw'
    have hwLeft := reachComponent_adj G D.cut D.left hv (hK v hvK w hwK hne)
      (reachComponent_outside G D.cut D.right w hw')
    exact Finset.disjoint_left.mp hdis hwLeft hw'
  · refine ⟨D, ?_⟩
    intro v hv hvK
    exact h ⟨v, hv, hvK⟩

end MinimalSeparator

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: SeparatorPaths -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem boundary_neighbor (Z : Finset V) (s : V) (hs : s ∈ Z)
    {a : V} (p : G.Walk a s) (ha : a ∉ Z)
    (hp : ∀ v ∈ p.support, v ∉ Z.erase s) :
    ∃ v, AvoidReach G Z a v ∧ G.Adj v s := by
  induction p with
  | nil => exact False.elim (ha hs)
  | @cons a b s hab p ih =>
    by_cases hb : b ∈ Z
    · have hbs : b = s := by
        by_contra hne
        exact hp b (List.mem_cons_of_mem _ p.start_mem_support)
          (Finset.mem_erase.mpr ⟨hne, hb⟩)
      exact ⟨a, AvoidReach.refl ha, hbs ▸ hab⟩
    · obtain ⟨v, hv, hvs⟩ := ih hs hb (fun v hv => hp v (List.mem_cons_of_mem _ hv))
      have hab' : AvoidReach G Z a b := (AvoidReach.refl ha).adj_step hab hb
      exact ⟨v, hab'.trans hv, hvs⟩

namespace MinimalSeparator

theorem neighbor_left (D : MinimalSeparator G) (s : V) (hs : s ∈ D.cut) :
    ∃ v ∈ reachComponent G D.cut D.left, G.Adj v s := by
  obtain ⟨p, hp⟩ := D.minimal s hs
  have hsm : s ∈ p.support := by
    by_contra hn
    apply D.separates
    refine ⟨p, ?_⟩
    intro v hv hvZ
    by_cases hvs : v = s
    · exact hn (hvs ▸ hv)
    · exact hp v hv (Finset.mem_erase.mpr ⟨hvs, hvZ⟩)
  obtain ⟨v, hv, hvs⟩ := boundary_neighbor D.cut s hs (p.takeUntil s hsm)
    D.left_outside (fun z hz => hp z (p.support_takeUntil_subset_support hsm hz))
  exact ⟨v, (mem_reachComponent _ _ _ _).mpr hv, hvs⟩

theorem neighbor_right (D : MinimalSeparator G) (s : V) (hs : s ∈ D.cut) :
    ∃ v ∈ reachComponent G D.cut D.right, G.Adj v s :=
  D.swap.neighbor_left s hs

theorem outside_path (D : MinimalSeparator G) (x y : V)
    (hx : x ∈ D.cut) (hy : y ∈ D.cut) :
    ∃ P : G.Walk x y, ∀ z ∈ P.support,
      z ∈ reachComponent G D.cut D.left ∪ D.cut → z = x ∨ z = y := by
  obtain ⟨u, hu, hux⟩ := D.neighbor_right x hx
  obtain ⟨v, hv, hvy⟩ := D.neighbor_right y hy
  have hru := (mem_reachComponent G D.cut D.right u).mp hu
  have hrv := (mem_reachComponent G D.cut D.right v).mp hv
  obtain ⟨Q, hQ⟩ := hru.symm.trans hrv
  have hQc : ∀ z ∈ Q.support, z ∈ reachComponent G D.cut D.right := by
    intro z hz
    exact (mem_reachComponent _ _ _ _).mpr (hru.trans (AvoidReach.support_reachable hQ hz))
  let P : G.Walk x y := .cons hux.symm (Q.concat hvy)
  refine ⟨P, ?_⟩
  intro z hz hzin
  simp only [P, Walk.support_cons, Walk.support_concat, List.mem_cons,
    List.mem_append, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | hz | rfl
  · exact Or.inl rfl
  · have hzr := hQc z hz
    rcases Finset.mem_union.mp hzin with hzl | hzs
    · exact False.elim (Finset.disjoint_left.mp
        (reachComponent_disjoint G D.cut D.left D.right D.separates) hzl hzr)
    · exact False.elim (reachComponent_outside G D.cut D.right z hzr hzs)
  · exact Or.inr rfl

end MinimalSeparator

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: HomeomorphEmbedding -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

theorem containsK4_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (hG : ContainsK4Homeomorph G) :
    ContainsK4Homeomorph H := by
  obtain ⟨b, p, hb, hp, hbranch, hdisj⟩ := hG
  refine ⟨fun i => f (b i), fun i j => (p i j).map f, hf.comp hb, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hp i j hij).map hf
  · intro i j hij k hk
    rw [SimpleGraph.Walk.support_map] at hk
    obtain ⟨v, hv, hve⟩ := List.mem_map.mp hk
    have he : v = b k := hf hve
    exact hbranch i j hij k (he ▸ hv)
  · intro i j k l hij hkl hne v hv hv'
    rw [SimpleGraph.Walk.support_map] at hv hv'
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hv
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hv'
    have he : x = y := hf (hxe.trans hye.symm)
    obtain ⟨q, hq⟩ := hdisj i j k l hij hkl hne x hx (he.symm ▸ hy)
    exact ⟨q, hxe.symm.trans (congrArg f hq)⟩

theorem seriesParallel_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (hH : IsSeriesParallel H) :
    IsSeriesParallel G := fun hG => hH (containsK4_of_embedding f hf hG)

theorem seriesParallel_induce {V : Type*} (G : SimpleGraph V)
    (hG : IsSeriesParallel G) (S : Set V) : IsSeriesParallel (G.induce S) :=
  seriesParallel_of_embedding (SimpleGraph.Embedding.induce (G := G) S).toHom
    (SimpleGraph.Embedding.induce (G := G) S).injective hG

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: VirtualEdgeLift -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open SimpleGraph

theorem lift_virtual_walk {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : W → V) (x y : W) (P : G.Walk (f x) (f y))
    (hP : ∀ z ∈ P.support, z ∈ Set.range f → z = f x ∨ z = f y)
    (hedge : ∀ a b, H.Adj a b →
      G.Adj (f a) (f b) ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    {a b : W} (p : H.Walk a b) :
    ∃ Q : G.Walk (f a) (f b),
      (∀ z ∈ Q.support, z ∈ Set.range f → ∃ w ∈ p.support, z = f w) ∧
      (∀ z ∈ Q.support, z ∉ Set.range f → x ∈ p.support ∧ y ∈ p.support) := by
  have hEdge : ∀ a b, H.Adj a b → ∃ Q : G.Walk (f a) (f b),
      (∀ z ∈ Q.support, z ∈ Set.range f → z = f a ∨ z = f b) ∧
      (∀ z ∈ Q.support, z ∉ Set.range f →
        (a = x ∧ b = y) ∨ (a = y ∧ b = x)) := by
    intro a b hab
    rcases hedge a b hab with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine ⟨.cons h .nil, ?_, ?_⟩
      · intro z hz _
        simpa only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] using hz
      · intro z hz hn
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> exact False.elim (hn ⟨_, rfl⟩)
    · subst a
      subst b
      exact ⟨P, hP, fun _ _ _ => Or.inl ⟨rfl, rfl⟩⟩
    · subst a
      subst b
      refine ⟨P.reverse, ?_, fun _ _ _ => Or.inr ⟨rfl, rfl⟩⟩
      intro z hz hf
      exact (hP z (by simpa using hz) hf).symm
  induction p with
  | @nil a =>
    refine ⟨.nil, ?_, ?_⟩
    · intro z hz _
      have he : z = f a := by simpa using hz
      exact ⟨a, by simp, he⟩
    · intro z hz hn
      have he : z = f a := by simpa using hz
      exact False.elim (hn ⟨a, he.symm⟩)
  | @cons a b c hab p ih =>
    obtain ⟨E, hEin, hEout⟩ := hEdge a b hab
    obtain ⟨Q, hQin, hQout⟩ := ih
    refine ⟨E.append Q, ?_, ?_⟩
    · intro z hz hf
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · rcases hEin z hz hf with he | he
        · exact ⟨a, List.mem_cons_self, he⟩
        · exact ⟨b, List.mem_cons_of_mem _ p.start_mem_support, he⟩
      · obtain ⟨w, hw, he⟩ := hQin z hz hf
        exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
    · intro z hz hf
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · rcases hEout z hz hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ p.start_mem_support⟩
        · subst a
          subst b
          exact ⟨List.mem_cons_of_mem _ p.start_mem_support, List.mem_cons_self⟩
      · obtain ⟨hx, hy⟩ := hQout z hz hf
        exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

private theorem ordered_pair_from_two (i j k l p q : Fin 4)
    (hij : i < j) (hkl : k < l) (hpq : p ≠ q)
    (hpi : p = i ∨ p = j) (hqi : q = i ∨ q = j)
    (hpk : p = k ∨ p = l) (hqk : q = k ∨ q = l) : (i,j) = (k,l) := by
  rcases hpi with hpi | hpi <;> rcases hqi with hqi | hqi <;>
    rcases hpk with hpk | hpk <;> rcases hqk with hqk | hqk <;>
    apply Prod.ext <;> dsimp only <;> omega

theorem containsK4_virtual_edge {V W : Type*} [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : W → V) (hf : Function.Injective f)
    (x y : W) (hxy : x ≠ y) (P : G.Walk (f x) (f y))
    (hP : ∀ z ∈ P.support, z ∈ Set.range f → z = f x ∨ z = f y)
    (hedge : ∀ a b, H.Adj a b →
      G.Adj (f a) (f b) ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hH : ContainsK4Homeomorph H) : ContainsK4Homeomorph G := by
  classical
  obtain ⟨b, p, hb, _hp, hbranch, hdisj⟩ := hH
  have hQ : ∀ i j, ∃ Q : G.Walk (f (b i)) (f (b j)), Q.IsPath ∧
      (∀ z ∈ Q.support, z ∈ Set.range f → ∃ w ∈ (p i j).support, z = f w) ∧
      (∀ z ∈ Q.support, z ∉ Set.range f → x ∈ (p i j).support ∧ y ∈ (p i j).support) := by
    intro i j
    obtain ⟨Q, hI, hO⟩ := lift_virtual_walk f x y P hP hedge (p i j)
    exact ⟨Q.bypass, Q.bypass_isPath,
      fun z hz => hI z (Q.support_bypass_subset_support hz),
      fun z hz => hO z (Q.support_bypass_subset_support hz)⟩
  choose Q hpath hI hO using hQ
  refine ⟨fun i => f (b i), Q, hf.comp hb, fun i j _ => hpath i j, ?_, ?_⟩
  · intro i j hij k hk
    obtain ⟨w, hw, he⟩ := hI i j _ hk ⟨b k, rfl⟩
    have hwe : b k = w := hf he
    exact hbranch i j hij k (hwe.symm ▸ hw)
  · intro i j k l hij hkl hne z hz hz'
    by_cases hfz : z ∈ Set.range f
    · obtain ⟨u, hu, he⟩ := hI i j z hz hfz
      obtain ⟨v, hv, he'⟩ := hI k l z hz' hfz
      have huv : u = v := hf (he.symm.trans he')
      obtain ⟨m, hm⟩ := hdisj i j k l hij hkl hne u hu (huv.symm ▸ hv)
      exact ⟨m, he.trans (congrArg f hm)⟩
    · obtain ⟨hx, hy⟩ := hO i j z hz hfz
      obtain ⟨hx', hy'⟩ := hO k l z hz' hfz
      obtain ⟨r, hr⟩ := hdisj i j k l hij hkl hne x hx hx'
      obtain ⟨s, hs⟩ := hdisj i j k l hij hkl hne y hy hy'
      have hrs : r ≠ s := by
        intro h
        exact hxy (hr.trans ((congrArg b h).trans hs.symm))
      have hri := hbranch i j hij r (hr ▸ hx)
      have hsi := hbranch i j hij s (hs ▸ hy)
      have hrk := hbranch k l hkl r (hr ▸ hx')
      have hsk := hbranch k l hkl s (hs ▸ hy')
      exact False.elim (hne (ordered_pair_from_two i j k l r s hij hkl hrs hri hsi hrk hsk))

theorem seriesParallel_virtual_edge {V W : Type*} [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph W} (hG : IsSeriesParallel G)
    (f : W → V) (hf : Function.Injective f) (x y : W) (hxy : x ≠ y)
    (P : G.Walk (f x) (f y))
    (hP : ∀ z ∈ P.support, z ∈ Set.range f → z = f x ∨ z = f y)
    (hedge : ∀ a b, H.Adj a b →
      G.Adj (f a) (f b) ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)) : IsSeriesParallel H :=
  fun hH => hG (containsK4_virtual_edge f hf x y hxy P hP hedge hH)

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: SeparatorCompletion -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace MinimalSeparator

noncomputable def region (D : MinimalSeparator G) : Finset V :=
  reachComponent G D.cut D.left ∪ D.cut

abbrev Region (D : MinimalSeparator G) := {v : V // v ∈ D.region}

noncomputable def completed (D : MinimalSeparator G) : SimpleGraph D.Region where
  Adj u v := G.Adj u.1 v.1 ∨ (u ≠ v ∧ u.1 ∈ D.cut ∧ v.1 ∈ D.cut)
  symm := by
    constructor
    intro u v h
    rcases h with h | ⟨hne, hu, hv⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, hv, hu⟩
  loopless := by
    constructor
    intro u h
    rcases h with h | h
    · exact G.loopless.irrefl u.1 h
    · exact h.1 rfl

noncomputable def boundary (D : MinimalSeparator G) : Finset D.Region := by
  classical
  exact Finset.univ.filter (fun v => v.1 ∈ D.cut)

@[simp] theorem mem_boundary (D : MinimalSeparator G) (v : D.Region) :
    v ∈ D.boundary ↔ v.1 ∈ D.cut := by
  classical
  simp [boundary]

theorem boundary_card (D : MinimalSeparator G) : D.boundary.card ≤ 2 := by
  classical
  have he : D.boundary.image Subtype.val = D.cut := by
    ext v
    simp only [Finset.mem_image, mem_boundary]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      exact ⟨⟨v, Finset.mem_union.mpr (Or.inr hv)⟩, hv, rfl⟩
  rw [← Finset.card_image_of_injective D.boundary Subtype.val_injective, he]
  exact D.small

theorem boundary_clique (D : MinimalSeparator G) :
    ∀ u ∈ D.boundary, ∀ v ∈ D.boundary, u ≠ v → D.completed.Adj u v := by
  intro u hu v hv hne
  exact Or.inr ⟨hne, (D.mem_boundary u).mp hu, (D.mem_boundary v).mp hv⟩

theorem outside_boundary (D : MinimalSeparator G) : ∃ v : D.Region, v ∉ D.boundary := by
  let v : D.Region := ⟨D.left, Finset.mem_union.mpr (Or.inl
    ((mem_reachComponent _ _ _ _).mpr (AvoidReach.refl D.left_outside)))⟩
  exact ⟨v, fun h => D.left_outside ((D.mem_boundary v).mp h)⟩

theorem region_card_lt (D : MinimalSeparator G) : Fintype.card D.Region < Fintype.card V := by
  classical
  have hne : D.region ≠ Finset.univ := by
    intro he
    exact D.right_not_union (by change D.right ∈ D.region; rw [he]; simp)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ D.region, hne⟩)
  simpa only [Fintype.card_coe, Finset.card_univ] using hlt

theorem completed_seriesParallel (D : MinimalSeparator G) (hG : IsSeriesParallel G) :
    IsSeriesParallel D.completed := by
  classical
  by_cases hpair : ∃ x ∈ D.cut, ∃ y ∈ D.cut, x ≠ y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
    have hcut : D.cut = {x,y} := by
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hx, hy⟩
      · simpa [hxy] using D.small
    let xx : D.Region := ⟨x, Finset.mem_union.mpr (Or.inr hx)⟩
    let yy : D.Region := ⟨y, Finset.mem_union.mpr (Or.inr hy)⟩
    obtain ⟨P, hP⟩ := D.outside_path x y hx hy
    apply seriesParallel_virtual_edge hG Subtype.val Subtype.val_injective xx yy
      (fun he => hxy (congrArg Subtype.val he)) P
    · intro z hz hr
      obtain ⟨u, rfl⟩ := hr
      exact hP u.1 hz u.2
    · intro a b hab
      rcases hab with hab | ⟨hne, ha, hb⟩
      · exact Or.inl hab
      · have ha' : a = xx ∨ a = yy := by
          simpa only [hcut, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] using ha
        have hb' : b = xx ∨ b = yy := by
          simpa only [hcut, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] using hb
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact False.elim (hne rfl)
        · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl,rfl⟩)
        · exact False.elim (hne rfl)
  · let f : D.completed →g G :=
      { toFun := Subtype.val
        map_rel' := by
          intro u v huv
          rcases huv with h | ⟨hne, hu, hv⟩
          · exact h
          · exact False.elim (hpair ⟨u.1, hu, v.1, hv,
              fun he => hne (Subtype.ext he)⟩) }
    exact seriesParallel_of_embedding f Subtype.val_injective hG

omit [DecidableEq V] in
private theorem subtype_degree_eq (S : Finset V) (H : SimpleGraph {v : V // v ∈ S})
    (v : {v : V // v ∈ S}) (hadj : ∀ w, H.Adj v w ↔ G.Adj v.1 w.1)
    (hsub : ∀ w, G.Adj v.1 w → w ∈ S) : H.degree v = G.degree v.1 := by
  classical
  let e : H.neighborSet v ≃ G.neighborSet v.1 :=
    { toFun := fun w => ⟨w.1.1, (hadj w.1).mp w.2⟩
      invFun := fun w => ⟨⟨w.1, hsub w.1 w.2⟩, (hadj _).mpr w.2⟩
      left_inv := fun w => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun w => by apply Subtype.ext; rfl }
  rw [← H.card_neighborSet_eq_degree v, ← G.card_neighborSet_eq_degree v.1]
  exact Fintype.card_congr e

theorem degree_completed (D : MinimalSeparator G) (v : D.Region) (hv : v ∉ D.boundary) :
    D.completed.degree v = G.degree v.1 := by
  classical
  have hvcut : v.1 ∉ D.cut := fun h => hv ((D.mem_boundary v).mpr h)
  have hvc : v.1 ∈ reachComponent G D.cut D.left :=
    (Finset.mem_union.mp v.2).resolve_right hvcut
  apply subtype_degree_eq D.region D.completed v
  · intro w
    change (G.Adj v.1 w.1 ∨ (v ≠ w ∧ v.1 ∈ D.cut ∧ w.1 ∈ D.cut)) ↔ G.Adj v.1 w.1
    exact or_iff_left (fun h => hvcut h.2.1)
  · intro w hw
    exact reachComponent_neighbor_union G D.cut D.left hvc hw

theorem outside_clique (D : MinimalSeparator G) (K : Finset V)
    (hK : ∀ v ∈ reachComponent G D.cut D.left, v ∉ K)
    (v : D.Region) (hv : v ∉ D.boundary) : v.1 ∉ K := by
  apply hK v.1
  exact (Finset.mem_union.mp v.2).resolve_right
    (fun h => hv ((D.mem_boundary v).mpr h))

end MinimalSeparator

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: FanToK4 -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

structure TrianglePaths {V : Type*} (G : SimpleGraph V) (C : Finset V) (b : Fin 3 → V) where
  path : ∀ i j, G.Walk (b i) (b j)
  simple : ∀ i j, i < j → (path i j).IsPath
  inside : ∀ i j, i < j → ∀ v ∈ (path i j).support, v ∈ C
  branch : ∀ i j, i < j → ∀ k, b k ∈ (path i j).support → k = i ∨ k = j
  disjoint : ∀ i j k l, i < j → k < l → (i,j) ≠ (k,l) →
    ∀ v, v ∈ (path i j).support → v ∈ (path k l).support → ∃ m, v = b m

theorem containsK4_of_fan_triangle {V : Type*} {G : SimpleGraph V} {a : V} {C : Finset V}
    (ha : a ∉ C) (F : ThreeFan G a C) (Q : TrianglePaths G C F.endpoint) :
    ContainsK4Homeomorph G := by
  let b : Fin 4 → V := Fin.cases a F.endpoint
  let p : ∀ i j : Fin 4, G.Walk (b i) (b j) :=
    Fin.cases (fun j => Fin.cases SimpleGraph.Walk.nil F.path j)
      (fun i j => Fin.cases (F.path i).reverse (fun j => Q.path i j) j)
  have hb : Function.Injective b := by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        have he : a = F.endpoint j := h
        exact False.elim (ha (he.symm ▸ F.target j))
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have he : F.endpoint i = a := h
        exact False.elim (ha (he ▸ F.target i))
      | succ j => exact congrArg Fin.succ (F.distinct h)
  refine ⟨b, p, hb, ?_, ?_, ?_⟩
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hij)
      | succ j => exact F.simple j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (Nat.not_lt_zero _ hij)
      | succ j => exact Q.simple i j (Fin.succ_lt_succ_iff.mp hij)
  · intro i j hij k hk
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hij)
      | succ j =>
        cases k using Fin.cases with
        | zero => exact Or.inl rfl
        | succ k =>
          have he := F.target_only j (F.endpoint k) hk (F.target k)
          exact Or.inr (congrArg Fin.succ (F.distinct he))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (Nat.not_lt_zero _ hij)
      | succ j =>
        have hij' := Fin.succ_lt_succ_iff.mp hij
        cases k using Fin.cases with
        | zero => exact False.elim (ha (Q.inside i j hij' a hk))
        | succ k =>
          rcases Q.branch i j hij' k hk with he | he
          · exact Or.inl (congrArg Fin.succ he)
          · exact Or.inr (congrArg Fin.succ he)
  · intro i j k l hij hkl hne v hv hv'
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hij)
      | succ j =>
        cases k using Fin.cases with
        | zero =>
          cases l using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hkl)
          | succ l =>
            have hjl : j ≠ l := fun he => hne (by simp [he])
            exact ⟨0, F.intersect j l hjl v hv hv'⟩
        | succ k =>
          cases l using Fin.cases with
          | zero => exact False.elim (Nat.not_lt_zero _ hkl)
          | succ l =>
            exact ⟨j.succ, F.target_only j v hv
              (Q.inside k l (Fin.succ_lt_succ_iff.mp hkl) v hv')⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (Nat.not_lt_zero _ hij)
      | succ j =>
        have hij' := Fin.succ_lt_succ_iff.mp hij
        cases k using Fin.cases with
        | zero =>
          cases l using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hkl)
          | succ l => exact ⟨l.succ, F.target_only l v hv' (Q.inside i j hij' v hv)⟩
        | succ k =>
          cases l using Fin.cases with
          | zero => exact False.elim (Nat.not_lt_zero _ hkl)
          | succ l =>
            have hne' : (i,j) ≠ (k,l) := by
              intro he
              obtain ⟨hi, hj⟩ := Prod.mk.inj he
              exact hne (by simp [hi, hj])
            obtain ⟨m, hm⟩ := Q.disjoint i j k l hij'
              (Fin.succ_lt_succ_iff.mp hkl) hne' v hv hv'
            exact ⟨m.succ, hm⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: WeakDuality -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem edge_sum_le (G : SimpleGraph V) (x : V → ℝ)
    (hx : OddCycleFeasible G x) (e : G.edgeSet) :
    (∑ u : V,if u∈(e : Sym2 V) then x u else 0) ≤ 1 := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : G.Adj a b := he
    have hne : a≠b := hab.ne
    have hs : (∑ u : V,if u∈s(a,b) then x u else 0)=x a+x b := by
      have hf : Finset.univ.filter (fun u => u∈s(a,b))={a,b} := by
        ext u
        simp
      rw [←Finset.sum_filter,hf,Finset.sum_pair hne]
    rw [hs]
    exact hx.2.1 a b hab

omit [DecidableEq V] in
private theorem sum_weighted_rows {I : Type*} [Fintype I]
    (a : I → V → Prop) [∀ i u,Decidable (a i u)] (z : I → ℝ) (x : V → ℝ) :
    (∑ u : V,(∑ i : I,if a i u then z i else 0)*x u) =
      ∑ i : I,z i*(∑ u : V,if a i u then x u else 0) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : a i u <;> simp [h]

theorem weak_duality (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℝ) (z : G.edgeSet → ℝ)
    (w : {C : Finset V // C∈oddCircuits G} → ℝ)
    (hx : OddCycleFeasible G x) (hd : DualFeasible G y z w) :
    primalValue x ≤ dualValue G y z w := by
  obtain ⟨hy,hz,hw,hcover⟩ := hd
  have hfirst : (∑ u : V,x u) ≤
      ∑ u : V,(y u+(∑ e : G.edgeSet,if u∈(e:Sym2 V) then z e else 0)+
        ∑ C : {C : Finset V // C∈oddCircuits G},if u∈C.val then w C else 0)*x u := by
    apply Finset.sum_le_sum
    intro u _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcover u) (hx.1 u).1
  have hedge : (∑ e : G.edgeSet,z e*(∑ u : V,if u∈(e:Sym2 V) then x u else 0)) ≤
      ∑ e : G.edgeSet,z e := by
    apply Finset.sum_le_sum
    intro e _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (edge_sum_le G x hx e) (hz e)
  have hcycle : (∑ C : {C : Finset V // C∈oddCircuits G},
      w C*(∑ u : V,if u∈C.val then x u else 0)) ≤
      ∑ C : {C : Finset V // C∈oddCircuits G},((C.val.card:ℝ)-1)/2*w C := by
    apply Finset.sum_le_sum
    intro C _
    have hh := mul_le_mul_of_nonneg_left (hx.2.2 C C.property) (hw C)
    simpa only [Finset.sum_ite_mem,Finset.univ_inter,mul_comm] using hh
  have hyx : (∑ u : V,y u*x u) ≤ ∑ u : V,y u := by
    apply Finset.sum_le_sum
    intro u _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hx.1 u).2 (hy u)
  dsimp [primalValue,dualValue]
  refine hfirst.trans ?_
  simp only [add_mul,Finset.sum_add_distrib]
  rw [sum_weighted_rows (fun (e:G.edgeSet) u => u∈(e:Sym2 V)) z x,
    sum_weighted_rows (fun (C : {C : Finset V // C∈oddCircuits G}) u => u∈C.val) w x]
  exact add_le_add (add_le_add hyx hedge) hcycle

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: StableVector -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def stableVector (S : Finset V) (v : V) : ℝ := if v∈S then 1 else 0

omit [Fintype V] in
theorem stableVector_edge (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) {u v : V} (h : G.Adj u v) :
    stableVector S u+stableVector S v ≤ 1 := by
  by_cases hu : u∈S <;> by_cases hv : v∈S
  · exact False.elim (hS hu hv h.ne h)
  · simp [stableVector,hu,hv]
  · simp [stableVector,hu,hv]
  · simp [stableVector,hu,hv]

private theorem cycle_next_adj (k : ℕ) (hk : 1≤k) (i : Fin (2*k+1)) :
    (SimpleGraph.cycleGraph (2*k+1)).Adj i (i+1) := by
  have : NeZero (2*k+1) := ⟨by omega⟩
  rw [SimpleGraph.cycleGraph_adj']
  right
  have he : i+1-i=(1:Fin (2*k+1)) := by abel
  rw [he]
  change 1 % (2*k+1)=1
  exact Nat.mod_eq_of_lt (by omega)

omit [Fintype V] in
theorem stableVector_odd (G : SimpleGraph V) (S C : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (hC : InducesOddCircuit G (C : Set V)) :
    (∑ u ∈ C,stableVector S u) ≤ ((C.card:ℝ)-1)/2 := by
  obtain ⟨k,hk,⟨e⟩⟩ := hC
  have : NeZero (2*k+1) := ⟨by omega⟩
  let a : Fin (2*k+1) → ℝ := fun i => stableVector S (e.symm i).val
  have hstep : ∀ i,a i+a (i+1)≤1 := by
    intro i
    exact stableVector_edge G S hS (e.symm.map_rel_iff.mpr (cycle_next_adj k hk i))
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hstep i)
  rw [Finset.sum_add_distrib] at hsum
  have hshift : (∑ i,a (i+1))=∑ i,a i := Equiv.sum_comp (Equiv.addRight (1:Fin (2*k+1))) a
  rw [hshift] at hsum
  have hcard : C.card=2*k+1 := by
    have hh := Fintype.card_congr e.toEquiv
    simpa using hh
  have hs : (∑ i,a i)=∑ u∈C,stableVector S u := by
    calc
      _ = ∑ u : C,stableVector S u.val := e.symm.toEquiv.sum_comp _
      _ = _ := Finset.sum_coe_sort C (stableVector S)
  rw [hs] at hsum
  have hv : (∑ u∈C,stableVector S u)=((C∩S).card:ℝ) := by
    simp [stableVector]
  rw [hv] at hsum ⊢
  have hn : (C∩S).card≤k := by
    have hh : ((C∩S).card:ℝ)+(C∩S).card≤2*k+1 := by simpa using hsum
    have hreal : (2:ℝ)*(C∩S).card≤2*k+1 := by linarith
    have hi : 2*(C∩S).card≤2*k+1 := by exact_mod_cast hreal
    omega
  rw [hcard]
  push_cast
  have hh : ((C∩S).card:ℝ)≤k := by exact_mod_cast hn
  linarith

theorem stableVector_feasible (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) : OddCycleFeasible G (stableVector S) := by
  refine ⟨?_,fun _ _ h => stableVector_edge G S hS h,?_⟩
  · intro u
    by_cases hu : u∈S <;> simp [stableVector,hu]
  · intro C hC
    apply stableVector_odd G S C hS
    exact (Finset.mem_filter.mp hC).2

theorem stableVector_value (S : Finset V) : primalValue (stableVector S)=(S.card:ℝ) := by
  simp [primalValue,stableVector]

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CoverData -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A block before chord refinement; the cycle need not be induced. -/
def IsBlock (G : SimpleGraph V) (W : Finset V) : Prop :=
  (∃ v,W={v}) ∨ (∃ u v,G.Adj u v ∧ W={u,v}) ∨
    ∃ k : ℕ,1≤k ∧ ∃ f : SimpleGraph.Copy (SimpleGraph.cycleGraph (2*k+1)) G,
      W=Finset.univ.image f

/-- A block whose row appears in the exact canonical dual. -/
def IsTightBlock (G : SimpleGraph V) (W : Finset V) : Prop :=
  (∃ v,W={v}) ∨ (∃ u v,G.Adj u v ∧ W={u,v}) ∨ InducesOddCircuit G (W : Set V)

structure BlockCover (G : SimpleGraph V) (U : Finset V) where
  parts : Finset (Finset V)
  good : ∀ W∈parts,IsBlock G W
  disjoint : (parts : Set (Finset V)).PairwiseDisjoint id
  covers : parts.biUnion id=U

structure TightCover (G : SimpleGraph V) (U : Finset V) where
  parts : Finset (Finset V)
  good : ∀ W∈parts,IsTightBlock G W
  disjoint : (parts : Set (Finset V)).PairwiseDisjoint id
  covers : parts.biUnion id=U

noncomputable def coverCost (P : Finset (Finset V)) : ℕ :=
  ∑ W∈P,componentValue W.card

theorem block_nonempty {G : SimpleGraph V} {W : Finset V} (h : IsBlock G W) : W.Nonempty := by
  rcases h with ⟨v,rfl⟩ | ⟨u,v,_h,rfl⟩ | ⟨k,hk,f,rfl⟩
  · exact Finset.singleton_nonempty _
  · exact ⟨u,by simp⟩
  · exact ⟨f ⟨0,by omega⟩,Finset.mem_image.mpr ⟨⟨0,by omega⟩,Finset.mem_univ _,rfl⟩⟩

omit [DecidableEq V] in
theorem oddCircuit_card (G : SimpleGraph V) (W : Finset V)
    (h : InducesOddCircuit G (W : Set V)) :
    ∃ k : ℕ,1≤k ∧ W.card=2*k+1 := by
  obtain ⟨k,hk,⟨e⟩⟩ := h
  refine ⟨k,hk,?_⟩
  have hh := Fintype.card_congr e.toEquiv
  simpa using hh

omit [DecidableEq V] in
theorem oddCircuit_value (G : SimpleGraph V) (W : Finset V)
    (h : InducesOddCircuit G (W : Set V)) :
    (componentValue W.card : ℝ)=((W.card:ℝ)-1)/2 := by
  obtain ⟨k,hk,hcard⟩ := oddCircuit_card G W h
  rw [hcard]
  have hn : ¬2*k+1≤2 := by omega
  simp only [componentValue,if_neg hn]
  have hsub : 2*k+1-1=2*k := by omega
  rw [hsub,Nat.mul_div_right k (by norm_num : 0<2)]
  push_cast
  ring

theorem cover_part_subset {G : SimpleGraph V} {U : Finset V}
    (P : BlockCover G U) {W : Finset V} (hW : W∈P.parts) : W⊆U := by
  intro v hv
  rw [←P.covers]
  exact Finset.mem_biUnion.mpr ⟨W,hW,hv⟩

theorem tight_part_subset {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) {W : Finset V} (hW : W∈P.parts) : W⊆U := by
  intro v hv
  rw [←P.covers]
  exact Finset.mem_biUnion.mpr ⟨W,hW,hv⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleWalks -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_support_card {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    p.support.toFinset.card=p.length := by
  have ht : p.tail.support.toFinset=p.support.toFinset := by
    rw [p.support_tail_of_not_nil hp.not_nil]
    rw [←p.cons_tail_support]
    simp only [List.tail_cons,List.toFinset_cons]
    exact (Finset.insert_eq_of_mem (List.mem_toFinset.mpr
      (p.end_mem_tail_support hp.not_nil))).symm
  rw [←ht,List.toFinset_card_of_nodup hp.isPath_tail.support_nodup]
  rw [Walk.length_support,Walk.length_tail]
  have hlen := hp.three_le_length
  omega

theorem cycle_presentation {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    ∃ (a b : V) (q : G.Walk a b),q.IsPath ∧ v∉q.support ∧ G.Adj v a ∧ G.Adj b v ∧
      q.length+2=p.length ∧ p.support.toFinset=insert v q.support.toFinset := by
  have ht : ¬p.tail.Nil := by
    rw [←Walk.length_eq_zero_iff,Walk.length_tail]
    have hh := hp.three_le_length
    omega
  let q := p.tail.dropLast
  have hsupport := p.tail.support_dropLast_concat ht
  have hnot : v∉q.support := by
    have hn := hp.isPath_tail.support_nodup
    rw [←hsupport,List.nodup_append] at hn
    intro hv
    exact hn.2.2 v hv v (by simp) rfl
  refine ⟨p.snd,p.tail.penultimate,q,hp.isPath_tail.dropLast,hnot,
    p.adj_snd hp.not_nil,p.tail.adj_penultimate ht,?_,?_⟩
  · dsimp [q]
    rw [Walk.length_dropLast,Walk.length_tail]
    have hh := hp.three_le_length
    omega
  · rw [←p.cons_tail_support]
    rw [←p.support_tail_of_not_nil hp.not_nil]
    rw [←hsupport]
    simp [q,List.toFinset_append,Finset.union_comm]

theorem copy_cycle_walk (k : ℕ) (hk : 1≤k)
    (f : SimpleGraph.Copy (cycleGraph (2*k+1)) G) :
    ∃ (v : V) (p : G.Walk v v),p.IsCycle ∧ p.length=2*k+1 ∧
      p.support.toFinset=Finset.univ.image f := by
  generalize hN : 2*k+1=N at f ⊢
  obtain ⟨n,rfl⟩ : ∃ n,N=n+3 := ⟨N-3,by omega⟩
  let q := cycleGraph.cycle n
  have hq : q.IsCycle := cycleGraph.isCycle_cycle
  have hs : q.support.toFinset=Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [cycle_support_card q hq]
    simp [q,cycleGraph.length_cycle]
  refine ⟨f 0,q.map f.toHom,?_,?_,?_⟩
  · exact (Walk.isCycle_map_iff_of_injective f.injective).mpr hq
  · simp [q,cycleGraph.length_cycle]
  · rw [Walk.support_map]
    have he : (q.support.map f.toHom).toFinset=q.support.toFinset.image f := by
      ext v
      simp
    rw [he,hs]

theorem cycle_walk_block {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (k : ℕ) (hk : 1≤k) (hlen : p.length=2*k+1) :
    IsBlock G p.support.toFinset := by
  let W := p.support.toFinset
  have hw : ∀u∈p.support,u∈(W : Set V) := fun u hu => List.mem_toFinset.mpr hu
  let q := p.induce (W : Set V) hw
  have hmap : q.map (SimpleGraph.Embedding.induce (G := G) (W : Set V)).toHom=p :=
    Walk.map_induce p hw
  have hq : q.IsCycle := by
    apply (Walk.isCycle_map_iff_of_injective (f := (SimpleGraph.Embedding.induce (G := G) (W : Set V)).toHom) (SimpleGraph.Embedding.induce (G := G) (W : Set V)).injective).mp
    rw [hmap]
    exact hp
  have hqLen : q.length=2*k+1 := by
    rw [←Walk.length_map (SimpleGraph.Embedding.induce (G := G) (W : Set V)).toHom, hmap]
    exact hlen
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2<2*k+1)).mpr
    ⟨_,q,hq,hqLen⟩
  let g := (SimpleGraph.Embedding.induce (G := G) (W : Set V)).toCopy.comp f
  refine Or.inr (Or.inr ⟨k,hk,g,?_⟩)
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    exact (f i).property
  · have hg : Function.Injective (fun i => g i) := g.injective
    rw [Finset.card_image_of_injective _ hg,Finset.card_univ,Fintype.card_fin]
    rw [cycle_support_card p hp,hlen]

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleSplitting -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_append_intersection {a b : V} (P : G.Walk a b) (Q : G.Walk b a)
    (h : (P.append Q).IsCycle) :
    ∀ z,z∈P.support → z∈Q.support → z=a ∨ z=b := by
  have hn := h.nodup_dropLast_support
  rw [Walk.support_append_eq_support_dropLast_append,
    List.dropLast_append_of_ne_nil Q.support_ne_nil,List.nodup_append] at hn
  intro z hzP hzQ
  by_cases hza : z=a
  · exact Or.inl hza
  by_cases hzb : z=b
  · exact Or.inr hzb
  have hp : z∈P.support.dropLast := by
    rw [←P.dropLast_support_concat,List.mem_append,List.mem_singleton] at hzP
    exact hzP.resolve_right hzb
  have hq : z∈Q.support.dropLast := by
    rw [←Q.dropLast_support_concat,List.mem_append,List.mem_singleton] at hzQ
    exact hzQ.resolve_right hza
  exact False.elim (hn.2.2 z hp z hq rfl)

theorem cycle_append_interior_disjoint {a b : V} (P : G.Walk a b) (Q : G.Walk b a)
    (h : (P.append Q).IsCycle) (hP : ¬P.Nil) (hQ : 2≤Q.length) :
    Disjoint P.support.toFinset Q.tail.dropLast.support.toFinset := by
  have hpQ := h.isPath_of_append_right hP
  have hQnil : ¬Q.Nil := by rw [←Walk.length_eq_zero_iff]; omega
  have hQt : ¬Q.tail.Nil := by
    rw [←Walk.length_eq_zero_iff,Walk.length_tail]
    omega
  have htail := hpQ.support_nodup
  rw [←Q.cons_tail_support,List.nodup_cons] at htail
  have hlast := hpQ.tail.support_nodup
  rw [←Q.tail.support_dropLast_concat hQt,List.nodup_append] at hlast
  apply Finset.disjoint_left.mpr
  intro z hzP hzQ
  have hzP' := List.mem_toFinset.mp hzP
  have hzQ' := List.mem_toFinset.mp hzQ
  have hzQt : z∈Q.tail.support := by
    rw [←Q.tail.support_dropLast_concat hQt]
    exact List.mem_append_left _ hzQ'
  have hzQs : z∈Q.support := by
    rw [Q.support_tail_of_not_nil hQnil] at hzQt
    exact List.mem_of_mem_tail hzQt
  rcases cycle_append_intersection P Q h z hzP' hzQs with hza | hzb
  · subst z
    exact hlast.2.2 a hzQ' a (by simp) rfl
  · subst z
    rw [Q.support_tail_of_not_nil hQnil] at hzQt
    exact htail.1 hzQt

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleTriangle -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem path_append_intersection {a b c : V} (P : G.Walk a b) (Q : G.Walk b c)
    (h : (P.append Q).IsPath) : ∀ z, z ∈ P.support → z ∈ Q.support → z = b := by
  have hn := h.support_nodup
  rw [Walk.support_append, List.nodup_append] at hn
  intro z hzP hzQ
  by_contra hne
  have hz : z ∈ Q.support.tail := by
    rw [← Walk.cons_tail_support Q, List.mem_cons] at hzQ
    exact hzQ.resolve_left hne
  exact hn.2.2 z hzP z hz rfl

theorem ordered_triangle_paths (C : Finset V) (b : Fin 3 → V) (hb : Function.Injective b)
    (A : G.Walk (b 0) (b 1)) (B : G.Walk (b 1) (b 2)) (D : G.Walk (b 2) (b 0))
    (hc : ((A.append B).append D).IsCycle)
    (hinside : ∀ v ∈ ((A.append B).append D).support, v ∈ C) :
    Nonempty (TrianglePaths G C b) := by
  have h02 : b 0 ≠ b 2 := fun h => by have he := congrArg Fin.val (hb h); norm_num at he
  have h01 : b 0 ≠ b 1 := fun h => by have he := congrArg Fin.val (hb h); norm_num at he
  have h12 : b 1 ≠ b 2 := fun h => by have he := congrArg Fin.val (hb h); norm_num at he
  have hAB : (A.append B).IsPath :=
    hc.isPath_of_append_left (Walk.not_nil_of_ne h02.symm)
  have hD : D.IsPath := hc.isPath_of_append_right (Walk.not_nil_of_ne h02)
  have hA : A.IsPath := hAB.of_append_left
  have hB : B.IsPath := hAB.of_append_right
  have hABi := path_append_intersection A B hAB
  have hAD : ∀ z, z ∈ A.support → z ∈ D.support → z = b 0 := by
    intro z hzA hzD
    have hzAB : z ∈ (A.append B).support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hzA)
    rcases cycle_append_intersection (A.append B) D hc z hzAB hzD with hz | hz
    · exact hz
    · have hza : b 2 ∈ A.support := hz ▸ hzA
      have hh := hABi (b 2) hza B.end_mem_support
      exact False.elim (h12 hh.symm)
  have hBD : ∀ z, z ∈ B.support → z ∈ D.support → z = b 2 := by
    intro z hzB hzD
    have hzAB : z ∈ (A.append B).support := (Walk.mem_support_append_iff _ _).mpr (Or.inr hzB)
    rcases cycle_append_intersection (A.append B) D hc z hzAB hzD with hz | hz
    · have hzb : b 0 ∈ B.support := hz ▸ hzB
      exact False.elim (h01 (hABi (b 0) A.start_mem_support hzb))
    · exact hz
  have hbrA : ∀ k, b k ∈ A.support → k = 0 ∨ k = 1 := by
    intro k hk
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (h12 (hABi (b 2) hk B.end_mem_support).symm)
  have hbrB : ∀ k, b k ∈ B.support → k = 1 ∨ k = 2 := by
    intro k hk
    fin_cases k
    · exact False.elim (h01 (hABi (b 0) A.start_mem_support hk))
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hbrD : ∀ k, b k ∈ D.support → k = 0 ∨ k = 2 := by
    intro k hk
    fin_cases k
    · exact Or.inl rfl
    · exact False.elim (h01 (hAD (b 1) A.end_mem_support hk).symm)
    · exact Or.inr rfl
  have hAs : ∀ v ∈ A.support, v ∈ C := by
    intro v hv
    exact hinside v ((Walk.mem_support_append_iff _ _).mpr
      (Or.inl ((Walk.mem_support_append_iff _ _).mpr (Or.inl hv))))
  have hBs : ∀ v ∈ B.support, v ∈ C := by
    intro v hv
    exact hinside v ((Walk.mem_support_append_iff _ _).mpr
      (Or.inl ((Walk.mem_support_append_iff _ _).mpr (Or.inr hv))))
  have hDs : ∀ v ∈ D.support, v ∈ C :=
    fun v hv => hinside v ((Walk.mem_support_append_iff _ _).mpr (Or.inr hv))
  let p : ∀ i j : Fin 3, G.Walk (b i) (b j) :=
    Fin.cases
      (Fin.cases .nil (Fin.cases A (Fin.cases D.reverse (fun i => Fin.elim0 i))))
      (Fin.cases
        (Fin.cases A.reverse (Fin.cases .nil (Fin.cases B (fun i => Fin.elim0 i))))
        (Fin.cases
          (Fin.cases D (Fin.cases B.reverse (Fin.cases .nil (fun i => Fin.elim0 i))))
          (fun i => Fin.elim0 i)))
  refine ⟨⟨p, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first | exact hA | exact hD.reverse | exact hB
  · intro i j hij v hv
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first
      | change v ∈ A.support at hv
      | change v ∈ B.support at hv
      | change v ∈ D.reverse.support at hv
    all_goals try simp only [Walk.support_reverse, List.mem_reverse] at hv
    all_goals first | exact hAs v hv | exact hBs v hv | exact hDs v hv
  · intro i j hij k hk
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first
      | change b k ∈ A.support at hk
      | change b k ∈ B.support at hk
      | change b k ∈ D.reverse.support at hk
    all_goals try simp only [Walk.support_reverse, List.mem_reverse] at hk
    all_goals first | exact hbrA k hk | exact hbrB k hk | exact hbrD k hk
  · intro i j k l hij hkl hne v hv hv'
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals fin_cases k <;> fin_cases l <;> norm_num at hkl
    all_goals first
      | change v ∈ A.support at hv
      | change v ∈ B.support at hv
      | change v ∈ D.reverse.support at hv
    all_goals first
      | change v ∈ A.support at hv'
      | change v ∈ B.support at hv'
      | change v ∈ D.reverse.support at hv'
    all_goals try simp only [Walk.support_reverse, List.mem_reverse] at hv hv'
    all_goals first
      | exact False.elim (hne rfl)
      | exact ⟨1, hABi v hv hv'⟩
      | exact ⟨1, hABi v hv' hv⟩
      | exact ⟨0, hAD v hv hv'⟩
      | exact ⟨0, hAD v hv' hv⟩
      | exact ⟨2, hBD v hv hv'⟩
      | exact ⟨2, hBD v hv' hv⟩

theorem cycle_ordered_parts {a b c : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hb : b ∈ p.support) (hc : c ∈ p.support) :
    ∃ (A : G.Walk a b) (B : G.Walk b c) (D : G.Walk c a),
      ((A.append B).append D).IsCycle ∧
      ∀ v ∈ ((A.append B).append D).support, v ∈ p.support := by
  let P := p.takeUntil b hb
  let Q := p.dropUntil b hb
  have he : P.append Q = p := p.take_spec hb
  have hparts : ∃ (A : G.Walk a b) (R : G.Walk b a),
      (A.append R).IsCycle ∧ c ∈ R.support ∧
      ∀ v ∈ (A.append R).support, v ∈ p.support := by
    by_cases hcQ : c ∈ Q.support
    · exact ⟨P, Q, he.symm ▸ hp, hcQ, fun v hv => he ▸ hv⟩
    · have hcP : c ∈ P.support := by
        rw [← he, Walk.mem_support_append_iff] at hc
        exact hc.resolve_right hcQ
      refine ⟨Q.reverse, P.reverse, ?_, by simpa using hcP, ?_⟩
      · rw [← Walk.reverse_append, he]
        exact hp.reverse
      · intro v hv
        rw [← Walk.reverse_append, he, Walk.support_reverse, List.mem_reverse] at hv
        exact hv
  obtain ⟨A, R, hAR, hcR, hsub⟩ := hparts
  refine ⟨A, R.takeUntil c hcR, R.dropUntil c hcR, ?_, ?_⟩
  · rw [← Walk.append_assoc, R.take_spec hcR]
    exact hAR
  · intro v hv
    rw [← Walk.append_assoc, R.take_spec hcR] at hv
    exact hsub v hv

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleFan -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open SimpleGraph

theorem containsK4_of_cycle_fan {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a v : V} (p : G.Walk v v) (hp : p.IsCycle) (ha : a ∉ p.support)
    (F : ThreeFan G a p.support.toFinset) : ContainsK4Homeomorph G := by
  have hb0 : F.endpoint 0 ∈ p.support := List.mem_toFinset.mp (F.target 0)
  let q := p.rotate (F.endpoint 0) hb0
  have hq : q.IsCycle := hp.rotate hb0
  have hb1 : F.endpoint 1 ∈ q.support :=
    (p.mem_support_rotate_iff _ hb0).mpr (List.mem_toFinset.mp (F.target 1))
  have hb2 : F.endpoint 2 ∈ q.support :=
    (p.mem_support_rotate_iff _ hb0).mpr (List.mem_toFinset.mp (F.target 2))
  obtain ⟨A, B, D, hc, hsub⟩ := cycle_ordered_parts q hq hb1 hb2
  obtain ⟨Q⟩ := ordered_triangle_paths p.support.toFinset F.endpoint F.distinct A B D hc
    (fun z hz => List.mem_toFinset.mpr ((p.mem_support_rotate_iff _ hb0).mp (hsub z hz)))
  exact containsK4_of_fan_triangle (by simpa using ha) F Q

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ThreeConnectedK4 -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem NoSmallSeparator.degree_three (hG : NoSmallSeparator G)
    (hV : 4 ≤ Fintype.card V) (v : V) : 3 ≤ G.degree v := by
  by_contra hdegree
  let Z := G.neighborFinset v
  have hZ : Z.card ≤ 2 := by change G.degree v ≤ 2; omega
  have hv : v ∉ Z := by simp [Z]
  have hex : ∃ w : V, w ∉ insert v Z := by
    by_contra! h
    have heq : insert v Z = Finset.univ := Finset.eq_univ_of_forall h
    have hc : (insert v Z).card = Z.card + 1 := Finset.card_insert_of_notMem hv
    rw [heq, Finset.card_univ] at hc
    omega
  obtain ⟨w, hw⟩ := hex
  have hw' : w ≠ v ∧ w ∉ Z := by simpa using hw
  obtain ⟨p, hp⟩ := hG Z hZ v w hv hw'.2
  cases p with
  | nil => exact hw'.1 rfl
  | cons h p =>
    exact hp _ (List.mem_cons_of_mem _ p.start_mem_support) ((G.mem_neighborFinset v _).mpr h)

theorem NoSmallSeparator.cycle_avoiding (hG : NoSmallSeparator G)
    (hV : 4 ≤ Fintype.card V) (a : V) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ a ∉ p.support := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hva⟩ := exists_ne a
  have hdeg := NoSmallSeparator.degree_three G hG hV v
  let N := (G.neighborFinset v).erase a
  have hN : 1 < N.card := by
    by_cases ha : a ∈ G.neighborFinset v
    · simp only [N, Finset.card_erase_of_mem ha, G.card_neighborFinset_eq_degree]
      omega
    · simp only [N, Finset.erase_eq_of_notMem ha, G.card_neighborFinset_eq_degree]
      omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hN
  have hu' : u ≠ a ∧ G.Adj v u := by simpa [N] using hu
  have hw' : w ≠ a ∧ G.Adj v w := by simpa [N] using hw
  have huZ : u ∉ ({a,v} : Finset V) := by simp [hu'.1, hu'.2.ne.symm]
  have hwZ : w ∉ ({a,v} : Finset V) := by simp [hw'.1, hw'.2.ne.symm]
  obtain ⟨p, hp⟩ := hG {a,v} (by simp [hva.symm]) u w huZ hwZ
  let P := p.bypass
  have hP : P.IsPath := p.bypass_isPath
  have hPa : a ∉ P.support := by
    intro h
    exact hp a (p.support_bypass_subset_support h) (by simp)
  have hPv : v ∉ P.support := by
    intro h
    exact hp v (p.support_bypass_subset_support h) (by simp)
  let Q : G.Walk u w := .cons hu'.2.symm (.cons hw'.2 .nil)
  have hQ : Q.IsPath := by
    simp [Q, Walk.isPath_def, hu'.2.ne.symm, hw'.2.ne, huw]
  have hQa : a ∉ Q.support := by
    simp [Q, hu'.1.symm, hva.symm, hw'.1.symm]
  have hne : P ≠ Q := by
    intro h
    apply hPv
    rw [h]
    simp [Q]
  obtain ⟨z, _hzP, _hzQ, c, hc, hsub⟩ := hP.exists_isCycle_sublist_of_ne hQ hne
  refine ⟨z, c, hc, ?_⟩
  intro ha
  have hm := hsub.subset ha
  rcases List.mem_append.mp hm with hm | hm
  · exact hPa hm
  · exact hQa (by simpa using List.mem_of_mem_tail hm)

theorem containsK4_of_noSmallSeparator (hG : NoSmallSeparator G)
    (hV : 4 ≤ Fintype.card V) : ContainsK4Homeomorph G := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a : V := Classical.choice inferInstance
  obtain ⟨v, p, hp, ha⟩ := NoSmallSeparator.cycle_avoiding G hG hV a
  have hcard : 3 ≤ p.support.toFinset.card := by
    rw [cycle_support_card p hp]
    exact hp.three_le_length
  have hfan := hG.fan_condition a p.support.toFinset hcard (by simpa using ha)
  obtain ⟨F⟩ := exists_three_fan G a p.support.toFinset hfan
  exact containsK4_of_cycle_fan p hp ha F

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: DiracLowDegree -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

universe u

private theorem protected_degree_induction (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (G : SimpleGraph V), IsSeriesParallel G →
      ∀ (K : Finset V), K.card ≤ 2 →
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) →
      (∃ v, v ∉ K) → ∃ v, v ∉ K ∧ G.degree v ≤ 2 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hn G hG K hKcard hK hex
    by_cases hnsmall : n ≤ 3
    · obtain ⟨v, hv⟩ := hex
      refine ⟨v, hv, ?_⟩
      have hdeg := G.degree_lt_card_verts v
      omega
    · have hn4 : 4 ≤ Fintype.card V := by omega
      have hsep : ¬ NoSmallSeparator G := by
        intro hconn
        exact hG (containsK4_of_noSmallSeparator G hconn hn4)
      obtain ⟨D⟩ := exists_minimalSeparator G hsep
      obtain ⟨D, hDK⟩ := D.choose_clique_side K hK
      have hlt : Fintype.card D.Region < n := by simpa only [hn] using D.region_card_lt
      obtain ⟨v, hv, hdegree⟩ := ih (Fintype.card D.Region) hlt D.Region rfl
        D.completed (D.completed_seriesParallel hG) D.boundary D.boundary_card
        D.boundary_clique D.outside_boundary
      refine ⟨v.1, D.outside_clique K hDK v hv, ?_⟩
      rwa [D.degree_completed v hv] at hdegree

theorem exists_degree_le_two_outside {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsSeriesParallel G) (K : Finset V) (hKcard : K.card ≤ 2)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) (hex : ∃ v, v ∉ K) :
    ∃ v, v ∉ K ∧ G.degree v ≤ 2 :=
  protected_degree_induction (Fintype.card V) V rfl G hG K hKcard hK hex

theorem exists_degree_le_two {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hG : IsSeriesParallel G) : ∃ v, G.degree v ≤ 2 := by
  classical
  obtain ⟨v, _, hv⟩ := exists_degree_le_two_outside G hG ∅ (by simp)
    (by simp) ⟨Classical.arbitrary V, by simp⟩
  exact ⟨v, hv⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: AttributedClosure -/
section
-- Prove2me | solution 1 for ChvatalPolytopes.SeriesParallel.deleteIdentify_isSeriesParallel
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:47:01.881997+00:00
-- url     : https://prove2.me/submissions/cde4be65-84c3-418d-b2ba-e40051abc57a




namespace ChvatalPolytopes.SeriesParallel

namespace DIAux

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (u v w : V)

def RS (z : V) : Prop := z = u ∨ z = v ∨ z = w

lemma val_RS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (x : {x : V // x ≠ u ∧ x ≠ w}) :
    RS u v w x.1 ↔ x = v' := by
  constructor
  · rintro (h | h | h)
    · exact absurd h x.2.1
    · exact Subtype.ext (h.trans hv'.symm)
    · exact absurd h x.2.2
  · rintro rfl; exact Or.inr (Or.inl hv')

lemma E1 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (ha : a ≠ v') (hb : b ≠ v') (h : (deleteIdentify G u v w).Adj a b) : G.Adj a.1 b.1 := by
  simp only [deleteIdentify, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, (h | h) | (h | h)⟩ := h
  · exact h
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) ha
  · exact h.symm
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) hb

lemma E2 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {c : {x : V // x ≠ u ∧ x ≠ w}}
    (h : (deleteIdentify G u v w).Adj v' c) : G.Adj v c.1 ∨ G.Adj w c.1 := by
  simp only [deleteIdentify, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, (h | h) | (h | h)⟩ := h
  · exact Or.inl (hv' ▸ h)
  · exact Or.inr h.2
  · exact Or.inl (hv' ▸ h.symm)
  · exact absurd (Subtype.ext (h.1.trans hv'.symm)) hne.symm

lemma L1 {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) :
    ∀ {a b : {x : V // x ≠ u ∧ x ≠ w}} (p : (deleteIdentify G u v w).Walk a b),
      v' ∉ p.support → ∃ Q : G.Walk a.1 b.1, Q.support = p.support.map Subtype.val
  | _, _, .nil, _ => ⟨Walk.nil, by simp⟩
  | a, _, .cons (v := c) h p, hp => by
    simp only [Walk.support_cons, List.mem_cons, not_or] at hp
    obtain ⟨Q, hQ⟩ := L1 hv' p hp.2
    have hc : c ≠ v' := by
      rintro rfl; exact hp.2 (Walk.start_mem_support _)
    exact ⟨Walk.cons (E1 G u v w hv' (Ne.symm hp.1) hc h) Q, by simp [hQ]⟩

lemma map_notRS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (l : List {x : V // x ≠ u ∧ x ≠ w})
    (hl : v' ∉ l) (z : V) (hz : z ∈ l.map Subtype.val) : ¬ RS u v w z := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
  rw [val_RS u v w hv']; rintro rfl; exact hl hx

lemma L2 (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {c b : {x : V // x ≠ u ∧ x ≠ w}}
    (h : (deleteIdentify G u v w).Adj v' c) (p : (deleteIdentify G u v w).Walk c b)
    (hp : p.IsPath) (hvp : v' ∉ p.support) (r : V) (hr : r = v ∨ r = w) :
    ∃ Q : G.Walk r b.1, Q.IsPath ∧ (∀ z ∈ Q.support, ¬ RS u v w z → z ∈ p.support.map Subtype.val) ∧
      (G.Adj r c.1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  obtain ⟨Q', hQ'⟩ := L1 G u v w hv' p hvp
  have hnd : (p.support.map Subtype.val).Nodup :=
    hp.support_nodup.map Subtype.val_injective
  have hnot := map_notRS u v w hv' _ hvp
  have hrR : RS u v w r := by rcases hr with rfl | rfl <;> simp [RS]
  have huR : RS u v w u := Or.inl rfl
  have hvR : RS u v w v := Or.inr (Or.inl rfl)
  have hwR : RS u v w w := Or.inr (Or.inr rfl)
  have huv' := huv.ne
  have huw' := huw.ne
  by_cases hc : G.Adj r c.1
  · refine ⟨Walk.cons hc Q', ?_, ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_cons, hQ', List.nodup_cons]
      exact ⟨fun hm => hnot _ hm hrR, hnd⟩
    · intro z hz hzR
      rw [Walk.support_cons, hQ', List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact absurd hrR hzR
      · exact hz
    · intro _ z hz hzR
      rw [Walk.support_cons, hQ', List.mem_cons] at hz
      rcases hz with rfl | hz
      · rfl
      · exact absurd hzR (hnot _ hz)
  · rcases hr with hr | hr <;> subst r
    · have hwc : G.Adj w c.1 := (E2 G u v w hv' h).resolve_left hc
      refine ⟨Walk.cons huv.symm (Walk.cons huw (Walk.cons hwc Q')), ?_, ?_, ?_⟩
      · rw [Walk.isPath_def]
        simp only [Walk.support_cons, hQ', List.nodup_cons, List.mem_cons, not_or]
        refine ⟨⟨huv'.symm, hvw, fun hm => hnot _ hm hvR⟩, ⟨huw', fun hm => hnot _ hm huR⟩,
          fun hm => hnot _ hm hwR, hnd⟩
      · intro z hz hzR
        simp only [Walk.support_cons, hQ', List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | hz
        · exact absurd hvR hzR
        · exact absurd huR hzR
        · exact absurd hwR hzR
        · exact hz
      · intro h'; exact absurd h' hc
    · have hvc : G.Adj v c.1 := (E2 G u v w hv' h).resolve_right hc
      refine ⟨Walk.cons huw.symm (Walk.cons huv (Walk.cons hvc Q')), ?_, ?_, ?_⟩
      · rw [Walk.isPath_def]
        simp only [Walk.support_cons, hQ', List.nodup_cons, List.mem_cons, not_or]
        refine ⟨⟨huw'.symm, hvw.symm, fun hm => hnot _ hm hwR⟩, ⟨huv', fun hm => hnot _ hm huR⟩,
          fun hm => hnot _ hm hvR, hnd⟩
      · intro z hz hzR
        simp only [Walk.support_cons, hQ', List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | hz
        · exact absurd hwR hzR
        · exact absurd huR hzR
        · exact absurd hvR hzR
        · exact hz
      · intro h'; exact absurd h' hc


lemma LPstart (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (p : (deleteIdentify G u v w).Walk a b) (ha : a = v')
    (hp : p.IsPath) (hb : b ≠ v') (r : V) (hr : r = v ∨ r = w) :
    ∃ Q : G.Walk r b.1, Q.IsPath ∧ (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ p.support, z = x.1) ∧
      (G.Adj r (p.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  cases p with
  | nil => exact absurd ha hb
  | cons h p' =>
    subst ha
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := L2 G u v w hvw huv huw hv' h p' hp.1 hp.2 r hr
    refine ⟨Q, hQ1, fun z hz hzR => ?_, fun hadj => hQ3 (by simpa using hadj)⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hQ2 z hz hzR)
    exact ⟨x, by simp [hx], rfl⟩

variable [DecidableEq V]

def sig (v' : {x : V // x ≠ u ∧ x ≠ w}) (r : V) (x : {x : V // x ≠ u ∧ x ≠ w}) : V :=
  if x = v' then r else x.1

lemma LP (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (r : V) (hr : r = v ∨ r = w)
    {a b : {x : V // x ≠ u ∧ x ≠ w}}
    (p : (deleteIdentify G u v w).Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    ∃ Q : G.Walk (sig u w v' r a) (sig u w v' r b), Q.IsPath ∧
      (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ p.support, z = x.1) ∧
      (∀ z ∈ Q.support, RS u v w z → v' ∈ p.support) ∧
      (a = v' → G.Adj r (p.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) ∧
      (b = v' → G.Adj r (p.reverse.getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) := by
  by_cases ha : a = v'
  · have hb : b ≠ v' := fun hb => hab (ha.trans hb.symm)
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := LPstart G u v w hvw huv huw hv' p ha hp hb r hr
    have e1 : r = sig u w v' r a := by simp [sig, ha]
    have e2 : b.1 = sig u w v' r b := by simp [sig, hb]
    refine ⟨Q.copy e1 e2, by simpa using hQ1, by simpa using hQ2, ?_, fun _ => by simpa using hQ3,
      fun hb' => absurd hb' hb⟩
    intro z _ _
    rw [← ha]; exact Walk.start_mem_support _
  by_cases hb : b = v'
  · obtain ⟨Q, hQ1, hQ2, hQ3⟩ := LPstart G u v w hvw huv huw hv' p.reverse hb hp.reverse ha r hr
    have e1 : a.1 = sig u w v' r a := by simp [sig, ha]
    have e2 : r = sig u w v' r b := by simp [sig, hb]
    refine ⟨Q.reverse.copy e1 e2, by simpa using hQ1.reverse, ?_, ?_, fun ha' => absurd ha' ha, ?_⟩
    · intro z hz hzR
      simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hz
      obtain ⟨x, hx, rfl⟩ := hQ2 z hz hzR
      exact ⟨x, by simpa using hx, rfl⟩
    · intro z _ _
      rw [← hb]; exact Walk.end_mem_support _
    · intro _ hadj z hz hzR
      simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hz
      exact hQ3 hadj z hz hzR
  have e1 : a.1 = sig u w v' r a := by simp [sig, ha]
  have e2 : b.1 = sig u w v' r b := by simp [sig, hb]
  by_cases hv : v' ∈ p.support
  · -- interior
    set p1 := p.takeUntil v' hv
    set p2 := p.dropUntil v' hv
    have hsp : p.support = p1.support ++ p2.support.tail := by
      rw [← Walk.support_append]; simp [p1, p2, Walk.take_spec]
    have hp1 : p1.IsPath := hp.takeUntil hv
    have hp2 : p2.IsPath := hp.dropUntil hv
    have hadjN : (deleteIdentify G u v w).Adj v' (p1.reverse.getVert 1) := by
      have hl : 0 < p1.reverse.length := by
        rcases Nat.eq_zero_or_pos p1.reverse.length with h0 | h0
        · exact absurd (Walk.eq_of_length_eq_zero h0).symm ha
        · exact h0
      simpa using p1.reverse.adj_getVert_succ hl
    obtain ⟨r0, hr0, hadj0⟩ : ∃ r0, (r0 = v ∨ r0 = w) ∧ G.Adj r0 (p1.reverse.getVert 1).1 := by
      rcases E2 G u v w hv' hadjN with h | h
      · exact ⟨v, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr rfl, h⟩
    obtain ⟨Q1, hQ11, hQ12, hQ13⟩ :=
      LPstart G u v w hvw huv huw hv' p1.reverse rfl hp1.reverse ha r0 hr0
    obtain ⟨Q2, hQ21, hQ22, -⟩ := LPstart G u v w hvw huv huw hv' p2 rfl hp2 hb r0 hr0
    have hQ13' := hQ13 hadj0
    have hpnd : (p1.support ++ p2.support.tail).Nodup := hsp ▸ hp.support_nodup
    refine ⟨(Q1.reverse.append Q2).copy e1 e2, ?_, ?_, fun _ _ _ => hv, fun h => absurd h ha,
      fun h => absurd h hb⟩
    · rw [Walk.isPath_def, Walk.support_copy, Walk.support_append, List.nodup_append]
      refine ⟨by simpa using hQ11.support_nodup, hQ21.support_nodup.sublist (List.tail_sublist _),
        ?_⟩
      intro z hz1 z' hz2 hzz
      subst hzz
      simp only [Walk.support_reverse, List.mem_reverse] at hz1
      have hQ2nd := hQ21.support_nodup
      rw [← Walk.cons_tail_support Q2, List.nodup_cons] at hQ2nd
      by_cases hzR : RS u v w z
      · have := hQ13' z hz1 hzR
        subst this
        exact hQ2nd.1 hz2
      · obtain ⟨x, hx, rfl⟩ := hQ12 _ hz1 hzR
        obtain ⟨y, hy, hxy⟩ := hQ22 _ (List.mem_of_mem_tail hz2) hzR
        have hxy' : x = y := Subtype.ext hxy
        subst hxy'
        have hxv : x ≠ v' := fun h => hzR ((val_RS u v w hv' x).2 h)
        rw [← Walk.cons_tail_support p2, List.mem_cons] at hy
        rcases hy with h | h
        · exact hxv h
        · simp only [Walk.support_reverse, List.mem_reverse] at hx
          exact List.disjoint_of_nodup_append hpnd hx h
    · intro z hz hzR
      rw [Walk.support_copy, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · simp only [Walk.support_reverse, List.mem_reverse] at hz
        obtain ⟨x, hx, rfl⟩ := hQ12 z hz hzR
        simp only [Walk.support_reverse, List.mem_reverse] at hx
        exact ⟨x, p.support_takeUntil_subset_support hv hx, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hQ22 z hz hzR
        exact ⟨x, p.support_dropUntil_subset_support hv hx, rfl⟩
  · obtain ⟨Q, hQ⟩ := L1 G u v w hv' p hv
    have hnot := map_notRS u v w hv' _ hv
    refine ⟨Q.copy e1 e2, ?_, ?_, fun z hz hzR => ?_, fun h => absurd h ha, fun h => absurd h hb⟩
    · rw [Walk.isPath_def, Walk.support_copy, hQ]
      exact hp.support_nodup.map Subtype.val_injective
    · intro z hz _
      rw [Walk.support_copy, hQ] at hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      exact ⟨x, hx, rfl⟩
    · rw [Walk.support_copy, hQ] at hz
      exact absurd hzR (hnot z hz)

lemma sig_RS {v' : {x : V // x ≠ u ∧ x ≠ w}} (hv' : v'.1 = v) (r : V) (hr : r = v ∨ r = w)
    (x : {x : V // x ≠ u ∧ x ≠ w}) : RS u v w (sig u w v' r x) ↔ x = v' := by
  unfold sig
  split_ifs with h
  · simp only [h, iff_true]; rcases hr with rfl | rfl <;> simp [RS]
  · rw [val_RS u v w hv']

lemma sig_ne {v' : {x : V // x ≠ u ∧ x ≠ w}} (r : V) {x : {x : V // x ≠ u ∧ x ≠ w}} (h : x ≠ v') :
    sig u w v' r x = x.1 := by simp [sig, h]

lemma sig_v' (v' : {x : V // x ≠ u ∧ x ≠ w}) (r : V) : sig u w v' r v' = r := by simp [sig]

lemma adj_first {W : Type*} {H : SimpleGraph W} {x y : W} (q : H.Walk x y) (h : x ≠ y) :
    H.Adj x (q.getVert 1) := by
  have hl : 0 < q.length := by
    rcases Nat.eq_zero_or_pos q.length with h0 | h0
    · exact absurd (Walk.eq_of_length_eq_zero h0) h
    · exact h0
  simpa using q.adj_getVert_succ hl

lemma comb : ∀ k m1 m2 m m' : Fin 4, m1 ≠ k → m2 ≠ k → m1 ≠ m2 → m ≠ k → m' ≠ k → m ≠ m' →
    m = m1 ∨ m = m2 ∨ m' = m1 ∨ m' = m2 := by decide

end DIAux

open SimpleGraph DIAux in
theorem deleteIdentify_isSeriesParallel_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (_hdeg : G.degree u = 2) (_hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by
  rintro ⟨b', p', hinj, hpath, hbr, hdisj⟩
  apply hG
  set v' : {x : V // x ≠ u ∧ x ≠ w} := ⟨v, huv.ne.symm, hvw⟩ with hv'def
  have hv' : v'.1 = v := rfl
  clear_value v'
  let Nb : Fin 4 → Fin 4 → {x : V // x ≠ u ∧ x ≠ w} := fun k m =>
    if k < m then (p' k m).getVert 1 else (p' m k).reverse.getVert 1
  have hNadj : ∀ k m, b' k = v' → m ≠ k → G.Adj v (Nb k m).1 ∨ G.Adj w (Nb k m).1 := by
    intro k m hk hm
    apply E2 G u v w hv'
    rw [← hk]
    have hne : b' k ≠ b' m := fun h => hm (hinj h).symm
    by_cases h : k < m
    · simp only [Nb, if_pos h]; exact adj_first _ hne
    · simp only [Nb, if_neg h]; exact adj_first _ hne
  obtain ⟨r, hr, hgood⟩ : ∃ r, (r = v ∨ r = w) ∧ ∀ k, b' k = v' → ∀ m m', m ≠ k → m' ≠ k →
      m ≠ m' → G.Adj r (Nb k m).1 ∨ G.Adj r (Nb k m').1 := by
    by_cases hex : ∃ k0, b' k0 = v'
    · obtain ⟨k0, hk0⟩ := hex
      have key : ∀ k, b' k = v' → k = k0 := fun k hk => hinj (hk.trans hk0.symm)
      by_cases hall : ∀ m m', m ≠ k0 → m' ≠ k0 → m ≠ m' →
          G.Adj v (Nb k0 m).1 ∨ G.Adj v (Nb k0 m').1
      · refine ⟨v, Or.inl rfl, fun k hk => ?_⟩
        obtain rfl := key k hk
        exact hall
      · push Not at hall
        obtain ⟨m1, m2, h1, h2, h12, hn1, hn2⟩ := hall
        refine ⟨w, Or.inr rfl, fun k hk m m' hm hm' hmm' => ?_⟩
        obtain rfl := key k hk
        rcases comb k m1 m2 m m' h1 h2 h12 hm hm' hmm' with rfl | rfl | rfl | rfl
        · exact Or.inl ((hNadj _ _ hk h1).resolve_left hn1)
        · exact Or.inl ((hNadj _ _ hk h2).resolve_left hn2)
        · exact Or.inr ((hNadj _ _ hk h1).resolve_left hn1)
        · exact Or.inr ((hNadj _ _ hk h2).resolve_left hn2)
    · exact ⟨v, Or.inl rfl, fun k hk => absurd ⟨k, hk⟩ hex⟩
  let b : Fin 4 → V := fun k => sig u w v' r (b' k)
  have hsR := sig_RS u v w hv' r hr
  have hQ : ∀ i j, ∃ Q : G.Walk (b i) (b j), i < j →
      (Q.IsPath ∧
      (∀ z ∈ Q.support, ¬ RS u v w z → ∃ x ∈ (p' i j).support, z = x.1) ∧
      (∀ z ∈ Q.support, RS u v w z → v' ∈ (p' i j).support) ∧
      (b' i = v' → G.Adj r ((p' i j).getVert 1).1 → ∀ z ∈ Q.support, RS u v w z → z = r) ∧
      (b' j = v' → G.Adj r ((p' i j).reverse.getVert 1).1 →
        ∀ z ∈ Q.support, RS u v w z → z = r)) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · obtain ⟨Q, hQ⟩ := LP G u v w hvw huv huw hv' r hr (p' i j) (hpath i j h)
        (fun e => h.ne (hinj e))
      exact ⟨Q, fun _ => hQ⟩
    · subst h; exact ⟨Walk.nil, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨Q, -⟩ := LP G u v w hvw huv huw hv' r hr (p' j i) (hpath j i h)
        (fun e => h.ne (hinj e))
      exact ⟨Q.reverse, fun h' => absurd h' (lt_asymm h)⟩
  choose Q hQ using hQ
  refine ⟨b, Q, ?_, fun i j h => (hQ i j h).1, ?_, ?_⟩
  · intro k l hkl
    apply hinj
    simp only [b] at hkl
    by_cases hk : b' k = v'
    · have : RS u v w (sig u w v' r (b' l)) := hkl ▸ (hsR _).2 hk
      rw [hsR] at this; rw [hk, this]
    · by_cases hl : b' l = v'
      · exact absurd ((hsR _).1 (hkl ▸ (hsR _).2 hl)) hk
      · rw [sig_ne u w r hk, sig_ne u w r hl] at hkl
        exact Subtype.ext hkl
  · intro i j hij k hk
    obtain ⟨_, A1, B1, -, -⟩ := hQ i j hij
    by_cases hR : RS u v w (b k)
    · have hk' : b' k = v' := (hsR _).1 hR
      exact hbr i j hij k (hk' ▸ B1 _ hk hR)
    · obtain ⟨x, hx, hxe⟩ := A1 _ hk hR
      have hk' : b' k ≠ v' := fun h => hR ((hsR _).2 h)
      have : b' k = x := Subtype.ext ((sig_ne u w r hk').symm.trans hxe)
      exact hbr i j hij k (this ▸ hx)
  · intro i j i' j' hij hij' hne z hz hz'
    obtain ⟨_, A1, B1, C1, D1⟩ := hQ i j hij
    obtain ⟨_, A2, B2, C2, D2⟩ := hQ i' j' hij'
    by_cases hzR : RS u v w z
    · have hv1 := B1 z hz hzR
      have hv2 := B2 z hz' hzR
      obtain ⟨k, hk⟩ := hdisj i j i' j' hij hij' hne v' hv1 hv2
      refine ⟨k, ?_⟩
      show z = sig u w v' r (b' k)
      rw [← hk, sig_v']
      have hk1 := hbr i j hij k (hk ▸ hv1)
      have hk2 := hbr i' j' hij' k (hk ▸ hv2)
      have hg := hgood k hk.symm
      rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl
      · have hjj : j ≠ j' := fun e => hne (by rw [e])
        rcases hg j j' hij.ne' hij'.ne' hjj with h | h
        · simp only [Nb, if_pos hij] at h; exact C1 hk.symm h z hz hzR
        · simp only [Nb, if_pos hij'] at h; exact C2 hk.symm h z hz' hzR
      · rcases hg j i' hij.ne' hij'.ne (by intro e; subst e; exact absurd (hij.trans hij') (lt_irrefl _)) with h | h
        · simp only [Nb, if_pos hij] at h; exact C1 hk.symm h z hz hzR
        · simp only [Nb, if_neg (lt_asymm hij')] at h; exact D2 hk.symm h z hz' hzR
      · rcases hg i j' hij.ne hij'.ne' (by intro e; subst e; exact absurd (hij.trans hij') (lt_irrefl _)) with h | h
        · simp only [Nb, if_neg (lt_asymm hij)] at h; exact D1 hk.symm h z hz hzR
        · simp only [Nb, if_pos hij'] at h; exact C2 hk.symm h z hz' hzR
      · have hii : i ≠ i' := fun e => hne (by rw [e])
        rcases hg i i' hij.ne hij'.ne hii with h | h
        · simp only [Nb, if_neg (lt_asymm hij)] at h; exact D1 hk.symm h z hz hzR
        · simp only [Nb, if_neg (lt_asymm hij')] at h; exact D2 hk.symm h z hz' hzR
    · obtain ⟨x, hx, rfl⟩ := A1 z hz hzR
      obtain ⟨y, hy, hxy⟩ := A2 _ hz' hzR
      obtain rfl : x = y := Subtype.ext hxy
      obtain ⟨k, rfl⟩ := hdisj i j i' j' hij hij' hne x hx hy
      refine ⟨k, ?_⟩
      have hk' : b' k ≠ v' := fun h => hzR ((val_RS u v w hv' _).2 h)
      exact (sig_ne u w r hk').symm

end ChvatalPolytopes.SeriesParallel

open ChvatalPolytopes.SeriesParallel


theorem checked_deleteIdentify_isSeriesParallel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u = 2) (hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by
  exact deleteIdentify_isSeriesParallel_core G hG u v w hvw huv huw hdeg hnadj

end

/- Complete checked body: CoverOperations -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem block_map {G : SimpleGraph V} {H : SimpleGraph W}
    (f : SimpleGraph.Copy G H) {A : Finset V} (hA : IsBlock G A) :
    IsBlock H (A.image f) := by
  rcases hA with ⟨v,rfl⟩ | ⟨u,v,huv,rfl⟩ | ⟨k,hk,g,rfl⟩
  · exact Or.inl ⟨f v,by simp⟩
  · exact Or.inr (Or.inl ⟨f u,f v,f.toHom.map_rel' huv,by simp⟩)
  · refine Or.inr (Or.inr ⟨k,hk,f.comp g,?_⟩)
    simp only [Finset.image_image]
    rfl

omit [DecidableEq V] in
theorem image_finset_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (fun A : Finset V => A.image f) := by
  intro A B h
  ext v
  have hh := congrArg (fun S : Finset W => f v∈S) h
  simpa [Finset.mem_image,hf.eq_iff] using hh

noncomputable def BlockCover.map {G : SimpleGraph V} {H : SimpleGraph W}
    {U : Finset V} (P : BlockCover G U) (f : SimpleGraph.Copy G H) :
    BlockCover H (U.image f) where
  parts := P.parts.image (fun A => A.image f)
  good := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact block_map f (P.good B hB)
  disjoint := by
    intro A hA B hB hne
    obtain ⟨A0,hA0,hAe⟩ := Finset.mem_image.mp hA
    obtain ⟨B0,hB0,hBe⟩ := Finset.mem_image.mp hB
    subst A
    subst B
    have hAB : A0≠B0 := fun h => hne (congrArg (fun A : Finset V => A.image f) h)
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    obtain ⟨u,hu,huw⟩ := Finset.mem_image.mp hwA
    obtain ⟨v,hv,hvw⟩ := Finset.mem_image.mp hwB
    have huv := f.injective (huw.trans hvw.symm)
    subst v
    exact Finset.disjoint_left.mp (P.disjoint hA0 hB0 hAB) hu hv
  covers := by
    ext w
    constructor
    · intro hw
      obtain ⟨A,hA,hwA⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hwA
      apply Finset.mem_image.mpr
      refine ⟨u,?_,rfl⟩
      rw [←P.covers]
      exact Finset.mem_biUnion.mpr ⟨B,hB,hu⟩
    · intro hw
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
      rw [←P.covers] at hu
      obtain ⟨B,hB,huB⟩ := Finset.mem_biUnion.mp hu
      apply Finset.mem_biUnion.mpr
      exact ⟨B.image f,Finset.mem_image.mpr ⟨B,hB,rfl⟩,
        Finset.mem_image.mpr ⟨u,huB,rfl⟩⟩

theorem BlockCover.cost_map {G : SimpleGraph V} {H : SimpleGraph W}
    {U : Finset V} (P : BlockCover G U) (f : SimpleGraph.Copy G H) :
    coverCost (P.map f).parts=coverCost P.parts := by
  unfold coverCost
  change (∑ A∈P.parts.image (fun A => A.image f),componentValue A.card)=_
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro A _
    have hf : Function.Injective (fun v => f v) := f.injective
    rw [Finset.card_image_of_injective _ hf]
  · intro A _ B _ h
    exact image_finset_injective f.injective h

noncomputable def BlockCover.empty (G : SimpleGraph V) : BlockCover G ∅ where
  parts := ∅
  good := by simp
  disjoint := by simp
  covers := by simp

noncomputable def BlockCover.one (G : SimpleGraph V) (A : Finset V)
    (hA : IsBlock G A) : BlockCover G A where
  parts := {A}
  good := by simpa using hA
  disjoint := by simp
  covers := by simp

theorem BlockCover.parts_disjoint {G : SimpleGraph V} {U W : Finset V}
    (P : BlockCover G U) (Q : BlockCover G W) (h : Disjoint U W) :
    Disjoint P.parts Q.parts := by
  apply Finset.disjoint_left.mpr
  intro A hAP hAQ
  obtain ⟨v,hv⟩ := block_nonempty (P.good A hAP)
  exact Finset.disjoint_left.mp h (cover_part_subset P hAP hv) (cover_part_subset Q hAQ hv)

noncomputable def BlockCover.union {G : SimpleGraph V} {U W : Finset V}
    (P : BlockCover G U) (Q : BlockCover G W) (h : Disjoint U W) :
    BlockCover G (U∪W) where
  parts := P.parts∪Q.parts
  good := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact P.good A hA
    · exact Q.good A hA
  disjoint := by
    intro A hA B hB hne
    rcases Finset.mem_union.mp hA with hA | hA <;>
      rcases Finset.mem_union.mp hB with hB | hB
    · exact P.disjoint hA hB hne
    · exact Finset.disjoint_of_subset_left (cover_part_subset P hA)
        (Finset.disjoint_of_subset_right (cover_part_subset Q hB) h)
    · exact Finset.disjoint_of_subset_left (cover_part_subset Q hA)
        (Finset.disjoint_of_subset_right (cover_part_subset P hB) h.symm)
    · exact Q.disjoint hA hB hne
  covers := by
    rw [Finset.union_biUnion,P.covers,Q.covers]

theorem BlockCover.cost_union {G : SimpleGraph V} {U W : Finset V}
    (P : BlockCover G U) (Q : BlockCover G W) (h : Disjoint U W) :
    coverCost (P.union Q h).parts=coverCost P.parts+coverCost Q.parts := by
  exact Finset.sum_union (P.parts_disjoint Q h)

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CoverMapOn -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq W] in
theorem block_changeGraph (G H : SimpleGraph V) (A : Finset V)
    (h : ∀ u∈A,∀ v∈A,G.Adj u v → H.Adj u v) (hA : IsBlock G A) : IsBlock H A := by
  rcases hA with ⟨v,rfl⟩ | ⟨u,v,huv,rfl⟩ | ⟨k,hk,f,rfl⟩
  · exact Or.inl ⟨v,rfl⟩
  · exact Or.inr (Or.inl ⟨u,v,h u (by simp) v (by simp) huv,rfl⟩)
  · let g : SimpleGraph.Copy (SimpleGraph.cycleGraph (2*k+1)) H :=
      { toHom :=
          { toFun := f
            map_rel' := fun {i j} hij => h (f i)
              (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) (f j)
              (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) (f.toHom.map_rel' hij) }
        injective' := f.injective }
    exact Or.inr (Or.inr ⟨k,hk,g,rfl⟩)

noncomputable def BlockCover.changeGraph {G : SimpleGraph V} {U : Finset V}
    (P : BlockCover G U) (H : SimpleGraph V)
    (h : ∀ u∈U,∀ v∈U,G.Adj u v → H.Adj u v) : BlockCover H U where
  parts := P.parts
  good := by
    intro A hA
    apply block_changeGraph G H A _ (P.good A hA)
    intro u hu v hv huv
    exact h u (cover_part_subset P hA hu) v (cover_part_subset P hA hv) huv
  disjoint := P.disjoint
  covers := P.covers

noncomputable def BlockCover.mapOn {G : SimpleGraph V} {H : SimpleGraph W}
    {U : Finset V} (P : BlockCover G U) (f : V → W) (hf : Function.Injective f)
    (h : ∀ u∈U,∀ v∈U,G.Adj u v → H.Adj (f u) (f v)) : BlockCover H (U.image f) :=
  (P.changeGraph (H.comap f) h).map (SimpleGraph.Embedding.comap ⟨f,hf⟩ H).toCopy

theorem BlockCover.cost_mapOn {G : SimpleGraph V} {H : SimpleGraph W}
    {U : Finset V} (P : BlockCover G U) (f : V → W) (hf : Function.Injective f)
    (h : ∀ u∈U,∀ v∈U,G.Adj u v → H.Adj (f u) (f v)) :
    coverCost (P.mapOn f hf h).parts=coverCost P.parts :=
  (P.changeGraph (H.comap f) h).cost_map (SimpleGraph.Embedding.comap ⟨f,hf⟩ H).toCopy

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ReductionStable -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem indep_insert (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (a : V) (ha : ∀v∈S,¬G.Adj a v) :
    G.IsIndepSet ((insert a S : Finset V) : Set V) := by
  intro u hu v hv hne huv
  rcases Finset.mem_insert.mp hu with hua | huS
  · subst u
    rcases Finset.mem_insert.mp hv with hva | hvS
    · subst v
      exact hne rfl
    · exact ha v hvS huv
  · rcases Finset.mem_insert.mp hv with hva | hvS
    · subst v
      exact ha u huS huv.symm
    · exact hS huS hvS hne huv

omit [Fintype V] [DecidableEq V] in
theorem deleteIdentify_adj_original (G : SimpleGraph V) (u v w : V)
    (a b : {x : V // x≠u ∧ x≠w}) (h : G.Adj a.val b.val) :
    (deleteIdentify G u v w).Adj a b := by
  rw [deleteIdentify,SimpleGraph.fromRel_adj]
  exact ⟨fun he => h.ne (congrArg Subtype.val he),Or.inl (Or.inl h)⟩

omit [Fintype V] in
theorem reduced_indep_image (G : SimpleGraph V) (u v w : V)
    (S : Finset {x : V // x≠u ∧ x≠w})
    (hS : (deleteIdentify G u v w).IsIndepSet (S : Set {x : V // x≠u ∧ x≠w})) :
    G.IsIndepSet (S.image Subtype.val : Set V) := by
  intro a ha b hb hne hab
  obtain ⟨a0,ha0,hea⟩ := Finset.mem_image.mp ha
  obtain ⟨b0,hb0,heb⟩ := Finset.mem_image.mp hb
  subst a
  subst b
  have hn : a0≠b0 := fun h => hne (congrArg Subtype.val h)
  exact hS ha0 hb0 hn (deleteIdentify_adj_original G u v w a0 b0 hab)

theorem neighbors_pair (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w) (hdeg : G.degree u=2) :
    ∀x,G.Adj u x → x=v ∨ x=w := by
  have hsub : ({v,w}:Finset V)⊆G.neighborFinset u := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact (G.mem_neighborFinset u v).mpr huv
    · have he : x=w := Finset.mem_singleton.mp hx
      subst x
      exact (G.mem_neighborFinset u w).mpr huw
  have heq : G.neighborFinset u={v,w} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le hsub
    change (G.neighborFinset u).card=2 at hdeg
    rw [hdeg,Finset.card_pair hvw]
  intro x hx
  have hh := (G.mem_neighborFinset u x).mpr hx
  rw [heq] at hh
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hh

theorem reduced_stable_lift (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u=2) (hnadj : ¬G.Adj v w)
    (r : {x : V // x≠u ∧ x≠w}) (hr : r.val=v)
    (S : Finset {x : V // x≠u ∧ x≠w})
    (hS : (deleteIdentify G u v w).IsIndepSet (S : Set {x : V // x≠u ∧ x≠w})) :
    ∃ T : Finset V,G.IsIndepSet (T : Set V) ∧ T.card=S.card+1 := by
  let A := S.image Subtype.val
  have hA := reduced_indep_image G u v w S hS
  have hcard : A.card=S.card := Finset.card_image_of_injective _ Subtype.val_injective
  have huA : u∉A := by
    rintro huA
    obtain ⟨x,_hx,hxu⟩ := Finset.mem_image.mp huA
    exact x.property.1 hxu
  have hwA : w∉A := by
    rintro hwA
    obtain ⟨x,_hx,hxw⟩ := Finset.mem_image.mp hwA
    exact x.property.2 hxw
  by_cases hrS : r∈S
  · refine ⟨insert w A,indep_insert G A hA w ?_,?_⟩
    · intro x hx hwx
      obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp hx
      subst x
      by_cases hzv : z.val=v
      · exact hnadj (hzv ▸ hwx.symm)
      · have hrz : r≠z := by intro he; exact hzv ((congrArg Subtype.val he).symm.trans hr)
        have hadj : (deleteIdentify G u v w).Adj r z := by
          rw [deleteIdentify,SimpleGraph.fromRel_adj]
          exact ⟨hrz,Or.inl (Or.inr ⟨hr,hwx⟩)⟩
        exact hS hrS hz hrz hadj
    · rw [Finset.card_insert_of_notMem hwA,hcard]
  · refine ⟨insert u A,indep_insert G A hA u ?_,?_⟩
    · intro x hx hux
      obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp hx
      subst x
      rcases neighbors_pair G u v w hvw huv huw hdeg z.val hux with he | he
      · have hzr : z=r := Subtype.ext (he.trans hr.symm)
        exact hrS (hzr ▸ hz)
      · exact z.property.2 he
    · rw [Finset.card_insert_of_notMem huA,hcard]

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CoverReplacement -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [DecidableEq V]

noncomputable def BlockCover.retarget {G : SimpleGraph V} {U W : Finset V}
    (P : BlockCover G U) (h : U=W) : BlockCover G W where
  parts := P.parts
  good := P.good
  disjoint := P.disjoint
  covers := P.covers.trans h

noncomputable def BlockCover.erase {G : SimpleGraph V} {U : Finset V}
    (P : BlockCover G U) (A : Finset V) (hA : A∈P.parts) : BlockCover G (U\A) where
  parts := P.parts.erase A
  good := fun W hW => P.good W (Finset.mem_of_mem_erase hW)
  disjoint := fun _ hW _ hZ hne =>
    P.disjoint (Finset.mem_of_mem_erase hW) (Finset.mem_of_mem_erase hZ) hne
  covers := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_sdiff,id_eq]
    constructor
    · rintro ⟨W,hW,hv⟩
      obtain ⟨hne,hW⟩ := Finset.mem_erase.mp hW
      refine ⟨cover_part_subset P hW hv,?_⟩
      intro hvA
      exact Finset.disjoint_left.mp (P.disjoint hW hA hne) hv hvA
    · rintro ⟨hvU,hvA⟩
      rw [←P.covers] at hvU
      obtain ⟨W,hW,hvW⟩ := Finset.mem_biUnion.mp hvU
      refine ⟨W,Finset.mem_erase.mpr ⟨?_,hW⟩,hvW⟩
      rintro rfl
      exact hvA hvW

theorem BlockCover.cost_erase {G : SimpleGraph V} {U : Finset V}
    (P : BlockCover G U) (A : Finset V) (hA : A∈P.parts) :
    coverCost (P.erase A hA).parts+componentValue A.card=coverCost P.parts := by
  exact Finset.sum_erase_add _ _ hA

theorem tight_isBlock {G : SimpleGraph V} {W : Finset V} (h : IsTightBlock G W) :
    IsBlock G W := by
  rcases h with h | h | ⟨k,hk,⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · let f := (SimpleGraph.Embedding.induce (G := G) (W : Set V)).toCopy.comp e.symm.toCopy
    refine Or.inr (Or.inr ⟨k,hk,f,?_⟩)
    ext v
    constructor
    · intro hv
      apply Finset.mem_image.mpr
      refine ⟨e ⟨v,hv⟩,Finset.mem_univ _,?_⟩
      simp [f]
    · intro hv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      exact (e.symm i).property

noncomputable def TightCover.toBlock {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) : BlockCover G U where
  parts := P.parts
  good := fun W hW => tight_isBlock (P.good W hW)
  disjoint := P.disjoint
  covers := P.covers

noncomputable def TightCover.retarget {G : SimpleGraph V} {U W : Finset V}
    (P : TightCover G U) (h : U=W) : TightCover G W where
  parts := P.parts
  good := P.good
  disjoint := P.disjoint
  covers := P.covers.trans h

noncomputable def TightCover.union {G : SimpleGraph V} {U W : Finset V}
    (P : TightCover G U) (Q : TightCover G W) (h : Disjoint U W) : TightCover G (U∪W) where
  parts := P.parts∪Q.parts
  good := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact P.good A hA
    · exact Q.good A hA
  disjoint := (P.toBlock.union Q.toBlock h).disjoint
  covers := (P.toBlock.union Q.toBlock h).covers

theorem TightCover.cost_union {G : SimpleGraph V} {U W : Finset V}
    (P : TightCover G U) (Q : TightCover G W) (h : Disjoint U W) :
    coverCost (P.union Q h).parts=coverCost P.parts+coverCost Q.parts :=
  P.toBlock.cost_union Q.toBlock h

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: DeletionLift -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lift_deleted_certificate (G : SimpleGraph V) (A : Finset V)
    (a : V) (ha : a∈A) (hneigh : ∀v,G.Adj a v → v∈A)
    (Q : BlockCover G A) (hQ : coverCost Q.parts≤1)
    (S : Finset {x : V // x∉A})
    (hS : (G.induce (A : Set V)ᶜ).IsIndepSet (S : Set {x : V // x∉A}))
    (P : BlockCover (G.induce (A : Set V)ᶜ) Finset.univ)
    (hP : coverCost P.parts≤S.card) :
    ∃ T : Finset V,G.IsIndepSet (T : Set V) ∧
      ∃ R : BlockCover G Finset.univ,coverCost R.parts≤T.card := by
  let B := S.image Subtype.val
  have hB : G.IsIndepSet (B : Set V) := by
    intro u hu v hv hne huv
    obtain ⟨u0,hu0,heu⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,hev⟩ := Finset.mem_image.mp hv
    subst u
    subst v
    exact hS hu0 hv0 (fun he => hne (congrArg Subtype.val he)) huv
  have haB : a∉B := by
    intro hh
    obtain ⟨x,_hx,hxa⟩ := Finset.mem_image.mp hh
    exact x.property (hxa.symm ▸ ha)
  have hT : G.IsIndepSet ((insert a B : Finset V) : Set V) := by
    apply indep_insert G B hB a
    intro v hv hav
    obtain ⟨v,_hv,rfl⟩ := Finset.mem_image.mp hv
    exact v.property (hneigh v hav)
  let f := (SimpleGraph.Embedding.induce (G := G) (A : Set V)ᶜ).toCopy
  let P' := P.map f
  have hd : Disjoint A (Finset.univ.image f) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hv
    obtain ⟨x,_hx,rfl⟩ := Finset.mem_image.mp hv
    exact x.property hvA
  have hu : A∪Finset.univ.image f=Finset.univ := by
    ext v
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    by_cases hv : v∈A
    · exact Or.inl hv
    · exact Or.inr ⟨⟨v,hv⟩,rfl⟩
  let R := (Q.union P' hd).retarget hu
  refine ⟨insert a B,hT,R,?_⟩
  have hBcard : B.card=S.card := Finset.card_image_of_injective _ Subtype.val_injective
  change coverCost (Q.union P' hd).parts≤_
  rw [BlockCover.cost_union,Finset.card_insert_of_notMem haB,hBcard]
  have hP' : coverCost P'.parts=coverCost P.parts := P.cost_map f
  omega

omit [Fintype V] in
theorem triangle_block (G : SimpleGraph V) (u v w : V)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    IsBlock G {u,v,w} := by
  let f : Fin 3 → V := ![u,v,w]
  have hinj : Function.Injective f := by
    intro i j h
    have h1 := huv.ne
    have h2 := huw.ne
    have h3 := hvw.ne
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hmap : ∀ {i j : Fin 3},(SimpleGraph.cycleGraph 3).Adj i j → G.Adj (f i) (f j) := by
    intro i j h
    have h1 := huv.symm
    have h2 := huw.symm
    have h3 := hvw.symm
    fin_cases i <;> fin_cases j <;>
      simp_all [f,SimpleGraph.cycleGraph_three_eq_top,SimpleGraph.top_adj]
  let F : SimpleGraph.Copy (SimpleGraph.cycleGraph 3) G := ⟨⟨f,hmap⟩,hinj⟩
  refine Or.inr (Or.inr ⟨1,by omega,F,?_⟩)
  ext x
  simp [F,f,Fin.exists_fin_succ,eq_comm]

omit [Fintype V] in
theorem triangle_cover (G : SimpleGraph V) (u v w : V)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    ∃ P : BlockCover G {u,v,w},coverCost P.parts=1 := by
  refine ⟨BlockCover.one G _ (triangle_block G u v w huv huw hvw),?_⟩
  have hcard : ({u,v,w}:Finset V).card=3 := by
    simp [Finset.card_insert_of_notMem,huv.ne,huw.ne,hvw.ne]
  simp only [BlockCover.one,coverCost,Finset.sum_singleton,hcard]
  norm_num [componentValue]

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: OutsidePath -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem close_outside_path {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (hlen : 1≤P.length) (c : V) (hc : c∉P.support)
    (hca : G.Adj c a) (hbc : G.Adj b c) :
    ∃ Q : G.Walk c c,Q.IsCycle ∧ Q.length=P.length+2 ∧
      Q.support.toFinset=insert c P.support.toFinset := by
  have ht : (P.concat hbc).IsPath := by
    rw [Walk.isPath_def,Walk.support_concat,List.nodup_append]
    refine ⟨hp.support_nodup,by simp,?_⟩
    intro x hx y hy hxy
    have hyc : y=c := List.mem_singleton.mp hy
    exact hc ((hxy.trans hyc) ▸ hx)
  let Q := Walk.cons hca (P.concat hbc)
  refine ⟨Q,?_,?_,?_⟩
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_,?_⟩
    · simpa [Q] using ht
    · simp only [Q,Walk.length_cons,Walk.length_concat]
      omega
  · simp only [Q,Walk.length_cons,Walk.length_concat]
  · ext x
    simp [Q,Walk.support_concat]

omit [DecidableEq V] in
theorem path_with_two_new_heads {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (u v : V) (hu : u∉P.support) (hv : v∉P.support)
    (huv : G.Adj u v) (hva : G.Adj v a) :
    (Walk.cons huv (Walk.cons hva P)).IsPath := by
  rw [Walk.isPath_def]
  simp only [Walk.support_cons,List.nodup_cons,List.mem_cons,not_or]
  exact ⟨⟨huv.ne,hu⟩,hv,hp.support_nodup⟩

theorem cycle_through_two_neighbors {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (u v w : V) (hu : u∉P.support) (hv : v∉P.support) (hw : w∉P.support)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hva : G.Adj v a) (hwb : G.Adj w b) :
    ∃ Q : G.Walk w w,Q.IsCycle ∧ Q.length=P.length+4 ∧
      Q.support.toFinset={u,v,w}∪P.support.toFinset := by
  let R := Walk.cons huv (Walk.cons hva P)
  have hR : R.IsPath := path_with_two_new_heads P hp u v hu hv huv hva
  have hwR : w∉R.support := by
    simp only [R,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨huw.ne.symm,hvw.symm,hw⟩
  obtain ⟨Q,hQ,hQl,hQs⟩ := close_outside_path R hR (by simp [R]) w hwR huw.symm hwb.symm
  refine ⟨Q,hQ,?_,?_⟩
  · simpa [R,Walk.length_cons,add_assoc] using hQl
  · rw [hQs]
    ext x
    simp only [R,Walk.support_cons,List.toFinset_cons,Finset.mem_insert,
      Finset.mem_union,Finset.mem_singleton]
    tauto

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleCovers -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem componentValue_odd (k : ℕ) (hk : 1≤k) : componentValue (2*k+1)=k := by
  have hn : ¬2*k+1≤2 := by omega
  simp only [componentValue,if_neg hn]
  have hs : 2*k+1-1=2*k := by omega
  rw [hs,Nat.mul_div_right k (by norm_num : 0<2)]

theorem cycle_cover {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (k : ℕ) (hk : 1≤k) (hlen : p.length=2*k+1) :
    ∃ P : BlockCover G p.support.toFinset,coverCost P.parts=k := by
  refine ⟨BlockCover.one G _ (cycle_walk_block p hp k hk hlen),?_⟩
  simp only [BlockCover.one,coverCost,Finset.sum_singleton]
  rw [cycle_support_card p hp,hlen,componentValue_odd k hk]

theorem same_neighbor_cover {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (u v w : V) (hu : u∉P.support) (hv : v∉P.support) (hw : w∉P.support)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (k : ℕ) (hk : 1≤k) (hlen : P.length+2=2*k+1) :
    ∃ R : BlockCover G ({u,v,w}∪P.support.toFinset),coverCost R.parts=k+1 := by
  obtain ⟨C,hC,hCl,hCs⟩ := close_outside_path P hp (by omega) v hv hva hvb.symm
  obtain ⟨Q,hQ⟩ := cycle_cover C hC k hk (hCl.trans hlen)
  let E := BlockCover.one G {u,w} (Or.inr (Or.inl ⟨u,w,huw,rfl⟩))
  have hE : coverCost E.parts=1 := by
    simp [E,BlockCover.one,coverCost,componentValue,Finset.card_pair huw.ne]
  have huC : u∉C.support.toFinset := by
    rw [hCs]
    simp only [Finset.mem_insert,List.mem_toFinset,not_or]
    exact ⟨huv.ne,hu⟩
  have hwC : w∉C.support.toFinset := by
    rw [hCs]
    simp only [Finset.mem_insert,List.mem_toFinset,not_or]
    exact ⟨hvw.symm,hw⟩
  have hd : Disjoint C.support.toFinset ({u,w}:Finset V) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxE
    rcases Finset.mem_insert.mp hxE with rfl | hxE
    · exact huC hx
    · have he : x=w := Finset.mem_singleton.mp hxE
      exact hwC (he ▸ hx)
  have heq : C.support.toFinset∪{u,w}={u,v,w}∪P.support.toFinset := by
    rw [hCs]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto
  refine ⟨(Q.union E hd).retarget heq,?_⟩
  change coverCost (Q.union E hd).parts=k+1
  rw [BlockCover.cost_union,hQ,hE]

theorem different_neighbor_cover {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (u v w : V) (hu : u∉P.support) (hv : v∉P.support) (hw : w∉P.support)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hva : G.Adj v a) (hwb : G.Adj w b)
    (k : ℕ) (hk : 1≤k) (hlen : P.length+2=2*k+1) :
    ∃ R : BlockCover G ({u,v,w}∪P.support.toFinset),coverCost R.parts=k+1 := by
  obtain ⟨C,hC,hCl,hCs⟩ := cycle_through_two_neighbors P hp u v w hu hv hw hvw huv huw hva hwb
  have hh : C.length=2*(k+1)+1 := by omega
  obtain ⟨Q,hQ⟩ := cycle_cover C hC (k+1) (by omega) hh
  exact ⟨Q.retarget hCs,hQ⟩

theorem neighbor_path_cover {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (u v w : V) (hu : u∉P.support) (hv : v∉P.support) (hw : w∉P.support)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (ha : G.Adj v a ∨ G.Adj w a) (hb : G.Adj v b ∨ G.Adj w b)
    (k : ℕ) (hk : 1≤k) (hlen : P.length+2=2*k+1) :
    ∃ R : BlockCover G ({u,v,w}∪P.support.toFinset),coverCost R.parts=k+1 := by
  have hswap : ({u,w,v}:Finset V)∪P.support.toFinset=({u,v,w}:Finset V)∪P.support.toFinset := by
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact same_neighbor_cover P hp u v w hu hv hw hvw huv huw ha hb k hk hlen
  · exact different_neighbor_cover P hp u v w hu hv hw hvw huv huw ha hb k hk hlen
  · have h := different_neighbor_cover P hp u w v hu hw hv hvw.symm huw huv ha hb k hk hlen
    obtain ⟨R,hR⟩ := h
    exact ⟨R.retarget hswap,hR⟩
  · have h := same_neighbor_cover P hp u w v hu hw hv hvw.symm huw huv ha hb k hk hlen
    obtain ⟨R,hR⟩ := h
    exact ⟨R.retarget hswap,hR⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ReductionCycle -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem reduced_cycle_cover (G : SimpleGraph V) (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (r : {x : V // x≠u ∧ x≠w}) (hr : r.val=v)
    (k : ℕ) (hk : 1≤k)
    (f : SimpleGraph.Copy (cycleGraph (2*k+1)) (deleteIdentify G u v w))
    (hrW : r∈Finset.univ.image f) :
    ∃ R : BlockCover G ((Finset.univ.image f).image Subtype.val∪{u,w}),
      coverCost R.parts=k+1 := by
  obtain ⟨z,p,hp,hlen,hsupp⟩ := copy_cycle_walk k hk f
  have hrp : r∈p.support := List.mem_toFinset.mp (hsupp.symm ▸ hrW)
  let c := p.rotate r hrp
  have hc : c.IsCycle := hp.rotate hrp
  have hclen : c.length=2*k+1 := by simpa only [c,Walk.length_rotate] using hlen
  have hcs : c.support.toFinset=Finset.univ.image f := by
    rw [←hsupp]
    ext x
    simp only [List.mem_toFinset,c,Walk.mem_support_rotate_iff]
  obtain ⟨a,b,q,hq,hrq,hra,hbr,hql,hqs⟩ := cycle_presentation c hc
  obtain ⟨Q,hQs⟩ := DIAux.L1 G u v w hr q hrq
  have hQ : Q.IsPath := by
    rw [Walk.isPath_def,hQs]
    exact hq.support_nodup.map Subtype.val_injective
  have hQlen : Q.length=q.length := by
    have hh := congrArg List.length hQs
    simp only [Walk.length_support,List.length_map] at hh
    omega
  have hnot : ∀x∈Q.support,¬DIAux.RS u v w x := by
    intro x hx
    rw [hQs] at hx
    exact DIAux.map_notRS u v w hr q.support hrq x hx
  have hu : u∉Q.support := fun h => hnot u h (Or.inl rfl)
  have hv : v∉Q.support := fun h => hnot v h (Or.inr (Or.inl rfl))
  have hw : w∉Q.support := fun h => hnot w h (Or.inr (Or.inr rfl))
  have ha : G.Adj v a.val ∨ G.Adj w a.val := DIAux.E2 G u v w hr hra
  have hb : G.Adj v b.val ∨ G.Adj w b.val := DIAux.E2 G u v w hr hbr.symm
  obtain ⟨R,hR⟩ := neighbor_path_cover Q hQ u v w hu hv hw hvw huv huw ha hb k hk (by omega)
  have hs : (Finset.univ.image f).image Subtype.val=insert v Q.support.toFinset := by
    rw [←hcs,hqs,Finset.image_insert,hr]
    congr 1
    ext x
    simp only [Finset.mem_image,List.mem_toFinset,hQs,List.mem_map]
  have heq : {u,v,w}∪Q.support.toFinset=(Finset.univ.image f).image Subtype.val∪{u,w} := by
    rw [hs]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto
  exact ⟨R.retarget heq,hR⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ReductionBlocks -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem two_edge_cover (G : SimpleGraph V) (a b c d : V)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hd : Disjoint ({a,b}:Finset V) {c,d}) :
    ∃ P : BlockCover G ({a,b}∪{c,d}),coverCost P.parts=2 := by
  let A := BlockCover.one G {a,b} (Or.inr (Or.inl ⟨a,b,hab,rfl⟩))
  let B := BlockCover.one G {c,d} (Or.inr (Or.inl ⟨c,d,hcd,rfl⟩))
  refine ⟨A.union B hd,?_⟩
  rw [BlockCover.cost_union]
  simp [A,B,BlockCover.one,coverCost,componentValue,Finset.card_pair hab.ne,
    Finset.card_pair hcd.ne]

theorem reduced_edge_cover (G : SimpleGraph V) (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (r x : {y : V // y≠u ∧ y≠w}) (hr : r.val=v)
    (h : (deleteIdentify G u v w).Adj r x) :
    ∃ P : BlockCover G (({r,x}:Finset _).image Subtype.val∪{u,w}),coverCost P.parts=2 := by
  have hxv : x.val≠v := by
    intro he
    exact h.ne (Subtype.ext (hr.trans he.symm))
  rcases DIAux.E2 G u v w hr h with hvx | hwx
  · have hd : Disjoint ({v,x.val}:Finset V) {u,w} := by
      simp [Finset.disjoint_left,huv.ne.symm,hvw,x.property.1,x.property.2]
    obtain ⟨P,hP⟩ := two_edge_cover G v x.val u w hvx huw hd
    have heq : ({v,x.val}:Finset V)∪{u,w}=({r,x}:Finset _).image Subtype.val∪{u,w} := by
      simp [hr]
    exact ⟨P.retarget heq,hP⟩
  · have hd : Disjoint ({w,x.val}:Finset V) {u,v} := by
      simp [Finset.disjoint_left,huw.ne.symm,hvw.symm,x.property.1,hxv]
    obtain ⟨P,hP⟩ := two_edge_cover G w x.val u v hwx huv hd
    have heq : ({w,x.val}:Finset V)∪{u,v}=({r,x}:Finset _).image Subtype.val∪{u,w} := by
      simp only [Finset.image_insert,Finset.image_singleton,hr]
      ext y
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact ⟨P.retarget heq,hP⟩

theorem reduced_singleton_cover (G : SimpleGraph V) (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (r : {y : V // y≠u ∧ y≠w}) (hr : r.val=v) :
    ∃ P : BlockCover G (({r}:Finset _).image Subtype.val∪{u,w}),coverCost P.parts=2 := by
  let A := BlockCover.one G {u,v} (Or.inr (Or.inl ⟨u,v,huv,rfl⟩))
  let B := BlockCover.one G {w} (Or.inl ⟨w,rfl⟩)
  have hd : Disjoint ({u,v}:Finset V) {w} := by
    simp [Finset.disjoint_left,huw.ne,hvw]
  let P := A.union B hd
  have hP : coverCost P.parts=2 := by
    rw [BlockCover.cost_union]
    simp [A,B,BlockCover.one,coverCost,componentValue,Finset.card_pair huv.ne]
  have heq : ({u,v}:Finset V)∪{w}=({r}:Finset _).image Subtype.val∪{u,w} := by
    simp only [Finset.image_singleton,hr]
    ext y
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  exact ⟨P.retarget heq,hP⟩

theorem reduced_block_cover (G : SimpleGraph V) (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (r : {y : V // y≠u ∧ y≠w}) (hr : r.val=v)
    (A : Finset {y : V // y≠u ∧ y≠w})
    (hA : IsBlock (deleteIdentify G u v w) A) (hrA : r∈A) :
    ∃ P : BlockCover G (A.image Subtype.val∪{u,w}),
      coverCost P.parts=componentValue A.card+1 := by
  rcases hA with ⟨x,rfl⟩ | ⟨x,y,hxy,rfl⟩ | ⟨k,hk,f,rfl⟩
  · have he : r=x := Finset.mem_singleton.mp hrA
    subst x
    obtain ⟨P,hP⟩ := reduced_singleton_cover G u v w hvw huv huw r hr
    refine ⟨P,?_⟩
    simpa [componentValue] using hP
  · have hrxy : r=x ∨ r=y := by simpa using hrA
    rcases hrxy with he | he
    · subst x
      obtain ⟨P,hP⟩ := reduced_edge_cover G u v w hvw huv huw r y hr hxy
      exact ⟨P,by simpa [Finset.card_pair hxy.ne,componentValue] using hP⟩
    · subst y
      obtain ⟨P,hP⟩ := reduced_edge_cover G u v w hvw huv huw r x hr hxy.symm
      have heq : ({r,x}:Finset _).image Subtype.val∪{u,w}=
          ({x,r}:Finset _).image Subtype.val∪{u,w} := by rw [Finset.pair_comm r x]
      refine ⟨P.retarget heq,?_⟩
      simpa [BlockCover.retarget,Finset.card_pair hxy.ne,componentValue] using hP
  · obtain ⟨P,hP⟩ := reduced_cycle_cover G u v w hvw huv huw r hr k hk f hrA
    refine ⟨P,?_⟩
    have hf : Function.Injective (fun i => f i) := f.injective
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin,componentValue_odd k hk]
    exact hP

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ReductionCover -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem reduced_cover_lift (G : SimpleGraph V) (u v w : V)
    (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (r : {y : V // y≠u ∧ y≠w}) (hr : r.val=v)
    (P : BlockCover (deleteIdentify G u v w) Finset.univ) :
    ∃ R : BlockCover G Finset.univ,coverCost R.parts=coverCost P.parts+1 := by
  have hrU : r∈P.parts.biUnion id := by rw [P.covers]; exact Finset.mem_univ _
  obtain ⟨A,hA,hrA⟩ := Finset.mem_biUnion.mp hrU
  let P0 := P.erase A hA
  have hadj : ∀ x∈(Finset.univ\A),∀ y∈(Finset.univ\A),
      (deleteIdentify G u v w).Adj x y → G.Adj x.val y.val := by
    intro x hx y hy hxy
    have hxr : x≠r := fun he => (Finset.mem_sdiff.mp hx).2 (he.symm ▸ hrA)
    have hyr : y≠r := fun he => (Finset.mem_sdiff.mp hy).2 (he.symm ▸ hrA)
    exact DIAux.E1 G u v w hr hxr hyr hxy
  let P1 := P0.mapOn Subtype.val Subtype.val_injective hadj
  obtain ⟨Q,hQ⟩ := reduced_block_cover G u v w hvw huv huw r hr A (P.good A hA) hrA
  have hd : Disjoint (A.image Subtype.val∪{u,w})
      ((Finset.univ\A).image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y0,hy0,hey⟩ := Finset.mem_image.mp hy
    subst x
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hx
      have he : z=y0 := Subtype.ext hzy
      exact (Finset.mem_sdiff.mp hy0).2 (he ▸ hz)
    · rcases Finset.mem_insert.mp hx with he | he
      · exact y0.property.1 he
      · exact y0.property.2 (Finset.mem_singleton.mp he)
  have heq : (A.image Subtype.val∪{u,w})∪((Finset.univ\A).image Subtype.val)=Finset.univ := by
    ext x
    simp only [Finset.mem_univ,iff_true]
    by_cases hxu : x=u
    · subst x
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
    by_cases hxw : x=w
    · subst x
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
    let y : {y : V // y≠u ∧ y≠w} := ⟨x,hxu,hxw⟩
    by_cases hyA : y∈A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨y,hyA,rfl⟩))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨y,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hyA⟩,rfl⟩)
  let R := (Q.union P1 hd).retarget heq
  refine ⟨R,?_⟩
  change coverCost (Q.union P1 hd).parts=coverCost P.parts+1
  rw [BlockCover.cost_union,hQ]
  have hP1 : coverCost P1.parts=coverCost P0.parts := P0.cost_mapOn _ _ _
  have hP0 : coverCost P0.parts+componentValue A.card=coverCost P.parts := P.cost_erase A hA
  omega

theorem reduced_certificate_lift (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) (hvw : v≠w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u=2) (hnadj : ¬G.Adj v w)
    (S : Finset {x : V // x≠u ∧ x≠w})
    (hS : (deleteIdentify G u v w).IsIndepSet (S : Set {x : V // x≠u ∧ x≠w}))
    (P : BlockCover (deleteIdentify G u v w) Finset.univ) (hP : coverCost P.parts≤S.card) :
    ∃ T : Finset V,G.IsIndepSet (T : Set V) ∧
      ∃ R : BlockCover G Finset.univ,coverCost R.parts≤T.card := by
  let r : {x : V // x≠u ∧ x≠w} := ⟨v,huv.ne.symm,hvw⟩
  obtain ⟨T,hT,hTc⟩ := reduced_stable_lift G u v w hvw huv huw hdeg hnadj r rfl S hS
  obtain ⟨R,hR⟩ := reduced_cover_lift G u v w hvw huv huw r rfl P
  refine ⟨T,hT,R,?_⟩
  omega

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: StableCoverInduction -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

universe u

abbrev HasStableCover {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V,G.IsIndepSet (S : Set V) ∧
    ∃ P : BlockCover G Finset.univ,coverCost P.parts≤S.card

private theorem stable_cover_aux (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V],Fintype.card V=n →
      ∀ G : SimpleGraph V,IsSeriesParallel G → HasStableCover G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hcard G hG
    by_cases hempty : IsEmpty V
    · let : IsEmpty V := hempty
      let P := (BlockCover.empty G).retarget (by simp : (∅ : Finset V)=Finset.univ)
      refine ⟨∅,by simp [SimpleGraph.IsIndepSet],P,?_⟩
      simp [P,BlockCover.retarget,BlockCover.empty,coverCost]
    · let : Nonempty V := not_isEmpty_iff.mp hempty
      obtain ⟨u,hdeg⟩ := exists_degree_le_two G hG
      have deletion (A : Finset V) (huA : u∈A)
          (hN : ∀v,G.Adj u v → v∈A) (Q : BlockCover G A)
          (hQ : coverCost Q.parts≤1) : HasStableCover G := by
        have hsmall : Fintype.card {x : V // x∉A}<n := by
          rw [←hcard]
          exact Fintype.card_subtype_lt (x := u) (by simpa using huA)
        obtain ⟨S,hS,P,hP⟩ := ih (Fintype.card {x : V // x∉A}) hsmall
          {x : V // x∉A} rfl (G.induce (A : Set V)ᶜ) (seriesParallel_induce G hG _)
        exact lift_deleted_certificate G A u huA hN Q hQ S hS P hP
      by_cases h0 : G.degree u=0
      · have hn : G.neighborFinset u=∅ := Finset.card_eq_zero.mp h0
        have hN : ∀v,G.Adj u v → v∈({u}:Finset V) := by
          intro v huv
          have hv := (G.mem_neighborFinset u v).mpr huv
          rw [hn] at hv
          exact False.elim (Finset.notMem_empty v hv)
        let Q := BlockCover.one G {u} (Or.inl ⟨u,rfl⟩)
        exact deletion {u} (by simp) hN Q (by simp [Q,BlockCover.one,coverCost,componentValue])
      by_cases h1 : G.degree u=1
      · obtain ⟨v,hn⟩ := Finset.card_eq_one.mp h1
        have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (by rw [hn]; simp)
        have hN : ∀x,G.Adj u x → x∈({u,v}:Finset V) := by
          intro x hux
          have hx := (G.mem_neighborFinset u x).mpr hux
          rw [hn] at hx
          have he : x=v := Finset.mem_singleton.mp hx
          simp [he]
        let Q := BlockCover.one G {u,v} (Or.inr (Or.inl ⟨u,v,huv,rfl⟩))
        exact deletion {u,v} (by simp) hN Q
          (by simp [Q,BlockCover.one,coverCost,componentValue,Finset.card_pair huv.ne])
      · have h2 : G.degree u=2 := by omega
        obtain ⟨v,w,hvw,hn⟩ := Finset.card_eq_two.mp h2
        have huv : G.Adj u v := (G.mem_neighborFinset u v).mp (by rw [hn]; simp)
        have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (by rw [hn]; simp)
        by_cases hvwadj : G.Adj v w
        · obtain ⟨Q,hQ⟩ := triangle_cover G u v w huv huw hvwadj
          have hN : ∀x,G.Adj u x → x∈({u,v,w}:Finset V) := by
            intro x hux
            rcases neighbors_pair G u v w hvw huv huw h2 x hux with he | he <;> simp [he]
          exact deletion {u,v,w} (by simp) hN Q hQ.le
        · have hsmall : Fintype.card {x : V // x≠u ∧ x≠w}<n := by
            rw [←hcard]
            exact Fintype.card_subtype_lt (x := u) (by simp)
          have hG' := checked_deleteIdentify_isSeriesParallel G hG u v w hvw huv huw h2 hvwadj
          obtain ⟨S,hS,P,hP⟩ := ih (Fintype.card {x : V // x≠u ∧ x≠w}) hsmall
            {x : V // x≠u ∧ x≠w} rfl (deleteIdentify G u v w) hG'
          exact reduced_certificate_lift G u v w hvw huv huw h2 hvwadj S hS P hP

theorem exists_stable_cover {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsSeriesParallel G) : HasStableCover G :=
  stable_cover_aux (Fintype.card V) V rfl G hG

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleInduced -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem copy_cycle_induced (k : ℕ) (hk : 1≤k)
    (f : SimpleGraph.Copy (cycleGraph (2*k+1)) G)
    (h : ∀ i j,G.Adj (f i) (f j) → (cycleGraph (2*k+1)).Adj i j) :
    InducesOddCircuit G (Finset.univ.image f : Set V) := by
  let e : cycleGraph (2*k+1) ↪g G :=
    { toEmbedding := ⟨f,f.injective⟩
      map_rel_iff' := fun {i j} => ⟨h i j,fun hh => f.toHom.map_rel' hh⟩ }
  have hs : Set.range e=(Finset.univ.image f : Set V) := by
    ext v
    simp [e]
  refine ⟨k,hk,?_⟩
  rw [←hs]
  exact ⟨e.isoInduceRange.symm⟩

omit [DecidableEq V] in
theorem nonedge_not_mem_mapped_walk {W : Type*} {H : SimpleGraph W}
    (f : SimpleGraph.Copy H G) {a b i j : W} (p : H.Walk a b)
    (h : ¬H.Adj i j) : s(f i,f j)∉(p.map f.toHom).edges := by
  intro hm
  rw [Walk.edges_map,List.mem_map] at hm
  obtain ⟨e,he,heq⟩ := hm
  have hs : e=s(i,j) := Sym2.map.injective f.injective heq
  rw [hs] at he
  exact h (p.adj_of_mem_edges he)

omit [DecidableEq V] in
theorem walk_two_le_of_missing_edge {a b : V} (p : G.Walk a b)
    (hne : a≠b) (hm : s(a,b)∉p.edges) : 2≤p.length := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons h p =>
    cases p with
    | nil => simp at hm
    | cons h' p => simp only [Walk.length_cons]; omega

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: PathMatching -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem even_path_cover (G : SimpleGraph V) (k : ℕ) :
    ∀ L : List V,L.Nodup → L.IsChain G.Adj → L.length=2*k →
      ∃ P : BlockCover G L.toFinset,coverCost P.parts=k ∧
        ∀ W∈P.parts,IsTightBlock G W := by
  induction k with
  | zero =>
    intro L _ _ hlen
    have hL : L=[] := List.length_eq_zero_iff.mp (by omega)
    subst L
    refine ⟨BlockCover.empty G,?_,?_⟩
    · simp [BlockCover.empty,coverCost]
    · simp [BlockCover.empty]
  | succ k ih =>
    intro L hnd hchain hlen
    cases L with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a L =>
      cases L with
      | nil => simp only [List.length_nil,List.length_cons] at hlen; omega
      | cons b L =>
        have hab : G.Adj a b := (List.isChain_cons_cons.mp hchain).1
        have htail := (List.isChain_cons_cons.mp hchain).2.tail
        have hndL : L.Nodup := hnd.tail.tail
        have hlenL : L.length=2*k := by simp only [List.length_cons] at hlen; omega
        obtain ⟨P,hP,hPt⟩ := ih L hndL htail hlenL
        let Q := BlockCover.one G {a,b} (Or.inr (Or.inl ⟨a,b,hab,rfl⟩))
        have hdis : Disjoint ({a,b}:Finset V) L.toFinset := by
          apply Finset.disjoint_left.mpr
          intro v hv hvL
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact (List.nodup_cons.mp hnd).1 (by simp only [List.mem_cons]; exact Or.inr (List.mem_toFinset.mp hvL))
          · exact (List.nodup_cons.mp hnd.tail).1 (List.mem_toFinset.mp hvL)
        let R := Q.union P hdis
        have hR : coverCost R.parts=k+1 := by
          rw [BlockCover.cost_union,hP]
          simp [Q,BlockCover.one,coverCost,componentValue,Finset.card_pair hab.ne,add_comm]
        have hRt : ∀W∈R.parts,IsTightBlock G W := by
          intro W hW
          rcases Finset.mem_union.mp hW with hW | hW
          · have he : W={a,b} := Finset.mem_singleton.mp hW
            exact Or.inr (Or.inl ⟨a,b,hab,he⟩)
          · exact hPt W hW
        have heq : ({a,b}:Finset V)∪L.toFinset=(a::b::L).toFinset := by simp
        rw [←heq]
        exact ⟨R,hR,hRt⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CycleSplitGeometry -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_split_union {a b : V} (P : G.Walk a b) (Q : G.Walk b a)
    (hQ : 2≤Q.length) :
    (P.append Q).support.toFinset=P.support.toFinset∪Q.tail.dropLast.support.toFinset := by
  have hQnil : ¬Q.Nil := by rw [←Walk.length_eq_zero_iff]; omega
  have hQt : ¬Q.tail.Nil := by rw [←Walk.length_eq_zero_iff,Walk.length_tail]; omega
  rw [Walk.support_append,←Q.support_tail_of_not_nil hQnil,
    ←Q.tail.support_dropLast_concat hQt]
  ext z
  simp only [List.mem_toFinset,List.mem_append,List.mem_singleton,Finset.mem_union]
  constructor
  · rintro (hz | hz | rfl)
    · exact Or.inl hz
    · exact Or.inr hz
    · exact Or.inl P.start_mem_support
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)

omit [DecidableEq V] in
theorem interior_support_length {a b : V} (Q : G.Walk a b) (hQ : 2≤Q.length) :
    Q.tail.dropLast.support.length=Q.length-1 := by
  rw [Walk.length_support,Walk.length_dropLast,Walk.length_tail]
  omega

theorem close_path_cycle {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (hlen : 2≤P.length) (hba : G.Adj b a) :
    (Walk.cons hba P).IsCycle ∧ (Walk.cons hba P).support.toFinset=P.support.toFinset := by
  constructor
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    exact ⟨by simpa using hp,by simp only [Walk.length_cons]; omega⟩
  · simp only [Walk.support_cons,List.toFinset_cons]
    exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr P.end_mem_support)

/-- The even arc of an odd cycle and the matching on the other arc's interior have exactly
its original cover value. -/
theorem even_arc_cover {a b : V} (P : G.Walk a b) (Q : G.Walk b a)
    (h : (P.append Q).IsCycle) (hP : 2≤P.length) (hQ : 2≤Q.length)
    (hba : G.Adj b a) (k l : ℕ) (hlen : (P.append Q).length=2*k+1)
    (hPlen : P.length=2*l) :
    ∃ A B : Finset V,Disjoint A B ∧ A∪B=(P.append Q).support.toFinset ∧
      A.card<(P.append Q).support.toFinset.card ∧ IsBlock G A ∧
      ∃ R : TightCover G B,componentValue A.card+coverCost R.parts=k := by
  have hPn : ¬P.Nil := by rw [←Walk.length_eq_zero_iff]; omega
  have hQn : ¬Q.Nil := by rw [←Walk.length_eq_zero_iff]; omega
  have hp := h.isPath_of_append_left hQn
  have hq := h.isPath_of_append_right hPn
  have hl : 1≤l := by omega
  let C := Walk.cons hba P
  obtain ⟨hC,hCs⟩ := close_path_cycle P hp hP hba
  have hClen : C.length=2*l+1 := by simp only [C,Walk.length_cons,hPlen]
  have hm : Q.length=2*(k-l)+1 := by rw [Walk.length_append,hPlen] at hlen; omega
  have hkl : l≤k := by rw [Walk.length_append,hPlen] at hlen; omega
  obtain ⟨R,hR,hRt⟩ := even_path_cover G (k-l) Q.tail.dropLast.support
    hq.tail.dropLast.support_nodup Q.tail.dropLast.isChain_adj_support (by
      rw [interior_support_length Q hQ,hm]
      omega)
  let T : TightCover G Q.tail.dropLast.support.toFinset :=
    ⟨R.parts,hRt,R.disjoint,R.covers⟩
  refine ⟨P.support.toFinset,Q.tail.dropLast.support.toFinset,
    cycle_append_interior_disjoint P Q h hPn hQ,(cycle_split_union P Q hQ).symm,
    ?_,?_,T,?_⟩
  · rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support,
      cycle_support_card (P.append Q) h,Walk.length_append]
    omega
  · rw [←hCs]
    exact cycle_walk_block C hC l hl hClen
  · have hcard : P.support.toFinset.card=2*l+1 := by
      rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support,hPlen]
    change componentValue P.support.toFinset.card+coverCost R.parts=k
    rw [hcard,hR]
    have hn : ¬2*l+1≤2 := by omega
    simp only [componentValue,if_neg hn]
    have hsub : 2*l+1-1=2*l := by omega
    rw [hsub,Nat.mul_div_right l (by norm_num : 0<2)]
    omega

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: ChordDecomposition -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical
open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem controlled_cycle (k : ℕ) (hk : 1≤k)
    (f : SimpleGraph.Copy (cycleGraph (2*k+1)) G) :
    ∃ (v : V) (p : G.Walk v v),p.IsCycle ∧ p.length=2*k+1 ∧
      p.support.toFinset=Finset.univ.image f ∧
      ∀ i j,¬(cycleGraph (2*k+1)).Adj i j → s(f i,f j)∉p.edges := by
  generalize hN : 2*k+1=N at f ⊢
  obtain ⟨n,rfl⟩ : ∃ n,N=n+3 := ⟨N-3,by omega⟩
  let q := cycleGraph.cycle n
  have hq : q.IsCycle := cycleGraph.isCycle_cycle
  have hs : q.support.toFinset=Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [cycle_support_card q hq]
    simp [q,cycleGraph.length_cycle]
  refine ⟨f 0,q.map f.toHom,?_,?_,?_,?_⟩
  · exact (Walk.isCycle_map_iff_of_injective f.injective).mpr hq
  · simp [q,cycleGraph.length_cycle]
  · rw [Walk.support_map]
    have he : (q.support.map f.toHom).toFinset=q.support.toFinset.image f := by ext v; simp
    rw [he,hs]
  · intro i j hij
    exact nonedge_not_mem_mapped_walk f q hij

theorem copy_cycle_decompose (k : ℕ) (hk : 1≤k)
    (f : SimpleGraph.Copy (cycleGraph (2*k+1)) G) :
    IsTightBlock G (Finset.univ.image f) ∨
      ∃ A B : Finset V,Disjoint A B ∧ A∪B=Finset.univ.image f ∧
        A.card<(Finset.univ.image f).card ∧ IsBlock G A ∧
        ∃ R : TightCover G B,componentValue A.card+coverCost R.parts=k := by
  by_cases hch : ∀ i j,G.Adj (f i) (f j) → (cycleGraph (2*k+1)).Adj i j
  · exact Or.inl (Or.inr (Or.inr (copy_cycle_induced k hk f hch)))
  · push Not at hch
    obtain ⟨i,j,hij,hnadj⟩ := hch
    obtain ⟨v,p,hp,hlen,hsupp,hmissing⟩ := controlled_cycle k hk f
    have hi : f i∈p.support := by
      apply List.mem_toFinset.mp
      rw [hsupp]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    let c := p.rotate (f i) hi
    have hc : c.IsCycle := hp.rotate hi
    have hclen : c.length=2*k+1 := by simpa only [c,Walk.length_rotate] using hlen
    have hcs : c.support.toFinset=Finset.univ.image f := by
      rw [←hsupp]
      ext z
      simp only [List.mem_toFinset,c,Walk.mem_support_rotate_iff]
    have hj : f j∈c.support := by
      apply List.mem_toFinset.mp
      rw [hcs]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    have hmiss : s(f i,f j)∉c.edges := by
      intro hh
      apply hmissing i j hnadj
      exact (p.rotate_edges (f i) hi).perm.mem_iff.mp hh
    let P := c.takeUntil (f j) hj
    let Q := c.dropUntil (f j) hj
    have hPQ : P.append Q=c := Walk.take_spec c hj
    have hcy : (P.append Q).IsCycle := hPQ.symm ▸ hc
    have hlenPQ : (P.append Q).length=2*k+1 := hPQ.symm ▸ hclen
    have hP : 2≤P.length := by
      apply walk_two_le_of_missing_edge P hij.ne
      intro hh
      apply hmiss
      rw [←hPQ,Walk.edges_append]
      exact List.mem_append_left _ hh
    have hQ : 2≤Q.length := by
      apply walk_two_le_of_missing_edge Q hij.ne.symm
      intro hh
      apply hmiss
      rw [←hPQ,Walk.edges_append]
      apply List.mem_append_right
      simpa only [Sym2.eq_swap] using hh
    apply Or.inr
    by_cases heven : P.length%2=0
    · have hPe : P.length=2*(P.length/2) := by omega
      obtain ⟨A,B,hd,hu,hsmall,hA,R,hcost⟩ :=
        even_arc_cover P Q hcy hP hQ hij.symm k (P.length/2) hlenPQ hPe
      rw [hPQ,hcs] at hu hsmall
      exact ⟨A,B,hd,hu,hsmall,hA,R,hcost⟩
    · have hQe : Q.length=2*(Q.length/2) := by
        rw [Walk.length_append] at hlenPQ
        omega
      have hcy' : (Q.reverse.append P.reverse).IsCycle := by
        rw [←Walk.reverse_append]
        exact hcy.reverse
      have hlen' : (Q.reverse.append P.reverse).length=2*k+1 := by
        simpa only [←Walk.reverse_append,Walk.length_reverse] using hlenPQ
      obtain ⟨A,B,hd,hu,hsmall,hA,R,hcost⟩ :=
        even_arc_cover Q.reverse P.reverse hcy' (by simpa using hQ) (by simpa using hP)
          hij.symm k (Q.length/2) hlen' (by simpa using hQe)
      have hs : (Q.reverse.append P.reverse).support.toFinset=Finset.univ.image f := by
        rw [←Walk.reverse_append,hPQ,Walk.support_reverse]
        simpa using hcs
      rw [hs] at hu hsmall
      exact ⟨A,B,hd,hu,hsmall,hA,R,hcost⟩

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CoverRefinement -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def TightCover.empty (G : SimpleGraph V) : TightCover G ∅ where
  parts := ∅
  good := by simp
  disjoint := by simp
  covers := by simp

noncomputable def TightCover.one (G : SimpleGraph V) (A : Finset V)
    (hA : IsTightBlock G A) : TightCover G A where
  parts := {A}
  good := by simpa using hA
  disjoint := by simp
  covers := by simp

private theorem refine_block_aux (n : ℕ) :
    ∀ W : Finset V,W.card=n → IsBlock G W →
      ∃ P : TightCover G W,coverCost P.parts≤componentValue W.card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W hcard hW
    rcases hW with hs | he | ⟨k,hk,f,rfl⟩
    · refine ⟨TightCover.one G W (Or.inl hs),?_⟩
      simp [TightCover.one,coverCost]
    · refine ⟨TightCover.one G W (Or.inr (Or.inl he)),?_⟩
      simp [TightCover.one,coverCost]
    · rcases copy_cycle_decompose k hk f with ht | ⟨A,B,hd,hu,hsmall,hA,R,hcost⟩
      · refine ⟨TightCover.one G _ ht,?_⟩
        simp [TightCover.one,coverCost]
      · obtain ⟨Q,hQ⟩ := ih A.card (hcard ▸ hsmall) A rfl hA
        let P := (Q.union R hd).retarget hu
        refine ⟨P,?_⟩
        have hf : Function.Injective (fun i => f i) := f.injective
        have hc : (Finset.univ.image f).card=2*k+1 := by
          rw [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin]
        have hv : componentValue (Finset.univ.image f).card=k := by
          rw [hc]
          have hn : ¬2*k+1≤2 := by omega
          simp only [componentValue,if_neg hn]
          have hh : 2*k+1-1=2*k := by omega
          rw [hh,Nat.mul_div_right k (by norm_num : 0<2)]
        change coverCost (Q.union R hd).parts≤_
        rw [TightCover.cost_union,hv]
        omega

theorem refine_block (W : Finset V) (hW : IsBlock G W) :
    ∃ P : TightCover G W,coverCost P.parts≤componentValue W.card :=
  refine_block_aux W.card W rfl hW

private theorem refine_cover_aux (n : ℕ) :
    ∀ (U : Finset V) (P : BlockCover G U),P.parts.card=n →
      ∃ Q : TightCover G U,coverCost Q.parts≤coverCost P.parts := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U P hcard
    by_cases hparts : P.parts=∅
    · have hU : U=∅ := by rw [←P.covers,hparts]; simp
      subst U
      refine ⟨TightCover.empty G,?_⟩
      simp [TightCover.empty,coverCost]
    · obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hparts
      have hsmall : (P.parts.erase A).card<n := by
        rw [←hcard]
        exact Finset.card_erase_lt_of_mem hA
      obtain ⟨R,hR⟩ := ih (P.parts.erase A).card hsmall (U\A) (P.erase A hA) rfl
      obtain ⟨Q,hQ⟩ := refine_block A (P.good A hA)
      have hd : Disjoint A (U\A) := by
        apply Finset.disjoint_left.mpr
        intro v hv hrest
        exact (Finset.mem_sdiff.mp hrest).2 hv
      have hu : A∪(U\A)=U := by
        ext v
        have hsub := cover_part_subset P hA
        simp only [Finset.mem_union,Finset.mem_sdiff]
        constructor
        · rintro (hv | ⟨hv,_⟩)
          · exact hsub hv
          · exact hv
        · intro hv
          by_cases ha : v∈A
          · exact Or.inl ha
          · exact Or.inr ⟨hv,ha⟩
      let T := (Q.union R hd).retarget hu
      refine ⟨T,?_⟩
      change coverCost (Q.union R hd).parts≤_
      rw [TightCover.cost_union]
      have he := P.cost_erase A hA
      omega

theorem refine_cover {U : Finset V} (P : BlockCover G U) :
    ∃ Q : TightCover G U,coverCost Q.parts≤coverCost P.parts :=
  refine_cover_aux P.parts.card U P rfl

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CoverDual -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev DualRow (G : SimpleGraph V) :=
  V ⊕ (G.edgeSet ⊕ {C : Finset V // C∈oddCircuits G})

def rowSupport (G : SimpleGraph V) : DualRow G → Finset V
  | .inl v => {v}
  | .inr (.inl e) => e.val.toFinset
  | .inr (.inr C) => C.val

noncomputable def rowCost (G : SimpleGraph V) : DualRow G → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr C) => ((C.val.card:ℝ)-1)/2

theorem tightBlock_row (G : SimpleGraph V) (W : Finset V) (h : IsTightBlock G W) :
    ∃ r : DualRow G,rowSupport G r=W ∧ rowCost G r=(componentValue W.card:ℝ) := by
  rcases h with ⟨v,rfl⟩ | ⟨u,v,huv,rfl⟩ | h
  · exact ⟨.inl v,rfl,by simp [rowCost,componentValue]⟩
  · refine ⟨.inr (.inl ⟨s(u,v),huv⟩),?_,?_⟩
    · exact Sym2.toFinset_mk_eq
    · simp [rowCost,Finset.card_pair huv.ne,componentValue]
  · refine ⟨.inr (.inr ⟨W,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩),rfl,?_⟩
    exact (oddCircuit_value G W h).symm

noncomputable def coverRow {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) (W : P.parts) : DualRow G :=
  Classical.choose (tightBlock_row G W (P.good W W.property))

theorem coverRow_spec {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) (W : P.parts) :
    rowSupport G (coverRow P W)=W.val ∧
      rowCost G (coverRow P W)=(componentValue W.val.card:ℝ) :=
  Classical.choose_spec (tightBlock_row G W (P.good W W.property))

theorem coverRow_injective {G : SimpleGraph V} {U : Finset V} (P : TightCover G U) :
    Function.Injective (coverRow P) := by
  intro A B h
  apply Subtype.ext
  rw [←(coverRow_spec P A).1,←(coverRow_spec P B).1,h]

noncomputable def coverRows {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) : Finset (DualRow G) := Finset.univ.image (coverRow P)

noncomputable def rowWeight {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) (r : DualRow G) : ℝ := if r∈coverRows P then 1 else 0

theorem rowWeight_binary {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) (r : DualRow G) : rowWeight P r=0 ∨ rowWeight P r=1 := by
  unfold rowWeight
  split_ifs <;> simp

theorem rowWeight_nonneg {G : SimpleGraph V} {U : Finset V}
    (P : TightCover G U) (r : DualRow G) : 0≤rowWeight P r := by
  rcases rowWeight_binary P r with h | h
  · simp [h]
  · simp [h]

theorem rowWeight_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TightCover G Finset.univ) (u : V) :
    1≤∑ r : DualRow G,if u∈rowSupport G r then rowWeight P r else 0 := by
  have hu : u∈P.parts.biUnion id := by rw [P.covers]; exact Finset.mem_univ _
  obtain ⟨W,hW,huW⟩ := Finset.mem_biUnion.mp hu
  let r := coverRow P ⟨W,hW⟩
  have hr : r∈coverRows P := Finset.mem_image.mpr ⟨⟨W,hW⟩,Finset.mem_univ _,rfl⟩
  have hus : u∈rowSupport G r := by rw [(coverRow_spec P ⟨W,hW⟩).1]; exact huW
  have hs := Finset.single_le_sum
    (f := fun r : DualRow G => if u∈rowSupport G r then rowWeight P r else 0)
    (fun r _ => by split_ifs; exact rowWeight_nonneg P r; exact le_rfl)
    (Finset.mem_univ r)
  simpa only [if_pos hus,rowWeight,if_pos hr] using hs

theorem rowWeight_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    {U : Finset V} (P : TightCover G U) :
    (∑ r : DualRow G,rowCost G r*rowWeight P r)=(coverCost P.parts:ℝ) := by
  calc
    _ = ∑ r∈coverRows P,rowCost G r := by simp [rowWeight,mul_ite]
    _ = ∑ W : P.parts,rowCost G (coverRow P W) :=
      Finset.sum_image (fun _ _ _ _ h => coverRow_injective P h)
    _ = ∑ W : P.parts,(componentValue W.val.card:ℝ) := by
      apply Finset.sum_congr rfl
      intro W _
      exact (coverRow_spec P W).2
    _ = _ := by
      have hh := Finset.sum_coe_sort P.parts (fun W => componentValue W.card)
      exact_mod_cast hh

theorem tightCover_dual (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TightCover G Finset.univ) :
    ∃ (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C∈oddCircuits G} → ℝ),
      (∀u,y u=0 ∨ y u=1) ∧ (∀e,z e=0 ∨ z e=1) ∧ (∀C,w C=0 ∨ w C=1) ∧
      DualFeasible G y z w ∧ dualValue G y z w=(coverCost P.parts:ℝ) := by
  let y := fun u : V => rowWeight P (.inl u)
  let z := fun e : G.edgeSet => rowWeight P (.inr (.inl e))
  let w := fun C : {C : Finset V // C∈oddCircuits G} => rowWeight P (.inr (.inr C))
  refine ⟨y,z,w,fun u => rowWeight_binary P _,fun e => rowWeight_binary P _,
    fun C => rowWeight_binary P _,?_,?_⟩
  · refine ⟨fun u => rowWeight_nonneg P _,fun e => rowWeight_nonneg P _,
      fun C => rowWeight_nonneg P _,?_⟩
    intro u
    have h := rowWeight_covers G P u
    simp only [Fintype.sum_sum_type,rowSupport,Finset.mem_singleton,Sym2.mem_toFinset,
      ] at h
    dsimp [y,z,w]
    rw [add_assoc]
    convert h using 1
    congr 2
    simp
  · have h := rowWeight_cost G P
    simpa [Fintype.sum_sum_type,rowCost,dualValue,y,z,w,add_assoc] using h

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: CertificateOptima -/
section

namespace ChvatalPolytopes.SeriesParallel.Proof

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem optima_of_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (P : TightCover G Finset.univ) (hc : coverCost P.parts≤S.card) :
    (∃ x : V → ℝ,(∀u,x u=0 ∨ x u=1) ∧ OddCycleFeasible G x ∧
      ∀x' : V → ℝ,OddCycleFeasible G x' → primalValue x'≤primalValue x) ∧
    (∃ (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C∈oddCircuits G} → ℝ),
      (∀u,y u=0 ∨ y u=1) ∧ (∀e,z e=0 ∨ z e=1) ∧ (∀C,w C=0 ∨ w C=1) ∧
      DualFeasible G y z w ∧
      ∀ (y' : V → ℝ) (z' : G.edgeSet → ℝ) (w' : {C : Finset V // C∈oddCircuits G} → ℝ),
        DualFeasible G y' z' w' → dualValue G y z w≤dualValue G y' z' w') := by
  obtain ⟨y,z,w,hy,hz,hw,hd,hvalue⟩ := tightCover_dual G P
  have hx := stableVector_feasible G S hS
  have hcmp : dualValue G y z w≤primalValue (stableVector S) := by
    rw [hvalue,stableVector_value]
    exact_mod_cast hc
  constructor
  · refine ⟨stableVector S,?_,hx,?_⟩
    · intro u
      by_cases hu : u∈S <;> simp [stableVector,hu]
    · intro x' hx'
      exact (weak_duality G x' y z w hx' hd).trans hcmp
  · refine ⟨y,z,w,hy,hz,hw,hd,?_⟩
    intro y' z' w' hd'
    exact hcmp.trans (weak_duality G (stableVector S) y' z' w' hx hd')

end ChvatalPolytopes.SeriesParallel.Proof

end

/- Complete checked body: OddCycleRoot -/
section

namespace ChvatalPolytopes.SeriesParallel

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G) :
    (∃ x : V → ℝ, (∀ u, x u = 0 ∨ x u = 1) ∧ OddCycleFeasible G x ∧
      ∀ x' : V → ℝ, OddCycleFeasible G x' → primalValue x' ≤ primalValue x) ∧
    (∃ (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C ∈ oddCircuits G} → ℝ),
      (∀ u, y u = 0 ∨ y u = 1) ∧ (∀ e, z e = 0 ∨ z e = 1) ∧ (∀ C, w C = 0 ∨ w C = 1) ∧
      DualFeasible G y z w ∧
      ∀ (y' : V → ℝ) (z' : G.edgeSet → ℝ) (w' : {C : Finset V // C ∈ oddCircuits G} → ℝ),
        DualFeasible G y' z' w' → dualValue G y z w ≤ dualValue G y' z' w') := by
  obtain ⟨S,hS,P,hP⟩ := Proof.exists_stable_cover G hG
  obtain ⟨Q,hQ⟩ := Proof.refine_cover P
  exact Proof.optima_of_certificate G S hS Q (hQ.trans hP)

end ChvatalPolytopes.SeriesParallel

end

open ChvatalPolytopes.SeriesParallel

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G) :
    (∃ x : V → ℝ, (∀ u, x u = 0 ∨ x u = 1) ∧ OddCycleFeasible G x ∧
      ∀ x' : V → ℝ, OddCycleFeasible G x' → primalValue x' ≤ primalValue x) ∧
    (∃ (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C ∈ oddCircuits G} → ℝ),
      (∀ u, y u = 0 ∨ y u = 1) ∧ (∀ e, z e = 0 ∨ z e = 1) ∧ (∀ C, w C = 0 ∨ w C = 1) ∧
      DualFeasible G y z w ∧
      ∀ (y' : V → ℝ) (z' : G.edgeSet → ℝ) (w' : {C : Finset V // C ∈ oddCircuits G} → ℝ),
        DualFeasible G y' z' w' → dualValue G y z w ≤ dualValue G y' z' w') := by
  exact ChvatalPolytopes.SeriesParallel.solution G hG

#print axioms ChvatalPolytopes.SeriesParallel.solution
#print axioms _root_.solution
