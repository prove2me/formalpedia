-- Prove2me | solution 1 for FlowsNetworks.DynamicFlow.max_dynamic_value_increment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:16:58.258983+00:00
-- url     : https://prove2.me/submissions/434d3dec-af6a-4c0f-9e2d-76cb735375d2

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network
import Definitions.Def_FlowsNetworks_DynamicFlow_DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

/-- the arc list of a node list -/
abbrev x8L (l : List N) : List (N × N) := List.zip l l.tail

lemma x8_zip_cons2 (x y : N) (rest : List N) :
    x8L (x :: y :: rest) = (x, y) :: x8L (y :: rest) := rfl

lemma x8_mem_L {l : List N} {q : N × N} (hq : q ∈ x8L l) :
    ∃ (i : ℕ) (h : i + 1 < l.length), q = (l[i], l[i + 1]) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have hl : i < l.length - 1 := by simpa using hi
  refine ⟨i, by omega, ?_⟩
  simp [List.getElem_zip, List.getElem_tail]

lemma x8_L_arcs (G : Network N) {s t : N} {l : List N} (hl : IsChainFromTo G s t l)
    {q : N × N} (hq : q ∈ x8L l) : q ∈ G.arcs := by
  obtain ⟨i, h, rfl⟩ := x8_mem_L hq
  exact hl.2.2.2.2 i h

/-- telescoping along a list -/
lemma x8_tele_list (w : N → ℝ) : ∀ (l : List N) (a b : N), l.head? = some a → l.getLast? = some b →
    ((x8L l).map (fun q => w q.2 - w q.1)).sum = w b - w a
  | [], a, b, h, _ => by simp at h
  | [x], a, b, h1, h2 => by simp at h1 h2; subst h1; subst h2; simp [x8L]
  | x :: y :: rest, a, b, h1, h2 => by
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      rw [x8_zip_cons2, List.map_cons, List.sum_cons,
        x8_tele_list w (y :: rest) y b rfl (by simpa using h2)]
      ring

/-- sums over a finset of arcs weighted by multiplicities -/
lemma x8_sum_count {M : Type*} [AddCommMonoid M] (S : Finset (N × N)) (F : N × N → M)
    (L : List (N × N)) (hL : ∀ q ∈ L, q ∈ S) :
    ∑ q ∈ S, L.count q • F q = (L.map F).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ← ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    simp only [List.count_cons, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (hL a List.mem_cons_self) h

lemma x8_traversal (G : Network N) (l : List N) :
    traversalTime G l = ((x8L l).map (fun q => G.cost q.1 q.2)).sum := by
  unfold traversalTime
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · rfl
    · simp only [List.tail_cons, List.zipWith_cons_cons] at ih ⊢
      rw [x8_zip_cons2, List.map_cons, ih]

lemma x8_timed_fst (G : Network N) : ∀ (l : List N) (τ0 : ℕ),
    (timedArcs G l τ0).map Prod.fst = x8L l
  | [], _ => by simp [timedArcs]
  | [x], _ => by simp [timedArcs]
  | x :: y :: rest, τ0 => by
      rw [timedArcs, List.map_cons, x8_timed_fst G (y :: rest), x8_zip_cons2]

/-- the per-copy conservation identity -/
lemma x8_cons_id (G : Network N) (θ : ℕ) (z : N) (τ : ℕ) : ∀ (l : List N) (τ0 : ℕ),
    (((timedArcs G l τ0).countP (fun e => e.1.1 = z ∧ θ + e.2 = τ) : ℕ) : ℤ) -
      (((timedArcs G l τ0).countP
        (fun e => e.1.2 = z ∧ θ + e.2 + G.cost e.1.1 e.1.2 = τ) : ℕ) : ℤ) =
      (if 2 ≤ l.length ∧ l.head? = some z ∧ τ = θ + τ0 then 1 else 0) -
      (if 2 ≤ l.length ∧ l.getLast? = some z ∧ τ = θ + τ0 + traversalTime G l then 1 else 0)
  | [], τ0 => by simp [timedArcs]
  | [x], τ0 => by simp [timedArcs]
  | x :: y :: rest, τ0 => by
      have ih := x8_cons_id G θ z τ (y :: rest) (τ0 + G.cost x y)
      rw [timedArcs, List.countP_cons, List.countP_cons]
      have htt : traversalTime G (x :: y :: rest) = G.cost x y + traversalTime G (y :: rest) := by
        simp [traversalTime, List.zipWith]
      rw [htt]
      have hlast : (x :: y :: rest).getLast? = (y :: rest).getLast? := by
        simp [List.getLast?_cons_cons]
      rw [hlast]
      push_cast
      rcases rest with _ | ⟨w, rest⟩
      · have h0 : traversalTime G [y] = 0 := rfl
        have hA : timedArcs G [y] (τ0 + G.cost x y) = [] := rfl
        simp only [hA, h0, List.countP_nil, List.length_cons, List.length_nil, List.head?_cons,
          List.getLast?_singleton, Option.some.injEq, decide_eq_true_eq] at ih ⊢
        have c1 : (if x = z ∧ θ + τ0 = τ then (1:ℤ) else 0) =
            if 2 ≤ 0 + 1 + 1 ∧ x = z ∧ τ = θ + τ0 then 1 else 0 :=
          if_congr ⟨fun h => ⟨by omega, h.1, by omega⟩, fun h => ⟨h.2.1, by omega⟩⟩ rfl rfl
        have c2 : (if y = z ∧ θ + τ0 + G.cost x y = τ then (1:ℤ) else 0) =
            if 2 ≤ 0 + 1 + 1 ∧ y = z ∧ τ = θ + τ0 + (G.cost x y + 0) then 1 else 0 :=
          if_congr ⟨fun h => ⟨by omega, h.1, by omega⟩, fun h => ⟨h.2.1, by omega⟩⟩ rfl rfl
        rw [c1, c2]; push_cast; ring
      · have h2 : 2 ≤ (y :: w :: rest).length := by simp
        simp only [h2, true_and, List.head?_cons, Option.some.injEq, List.length_cons,
          decide_eq_true_eq] at ih ⊢
        have : 2 ≤ rest.length + 1 + 1 + 1 := by omega
        simp only [this, true_and]
        have c1 : (if x = z ∧ θ + τ0 = τ then (1:ℤ) else 0) = if x = z ∧ τ = θ + τ0 then 1 else 0 :=
          if_congr ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩ rfl rfl
        have c2 : (if y = z ∧ θ + τ0 + G.cost x y = τ then (1:ℤ) else 0) =
            if 2 ≤ rest.length + 1 + 1 ∧ y = z ∧ τ = θ + (τ0 + G.cost x y) then 1 else 0 :=
          if_congr ⟨fun h => ⟨by omega, h.1, by omega⟩, fun h => ⟨h.2.1, by omega⟩⟩ rfl rfl
        have c3 : (if (y :: w :: rest).getLast? = some z ∧
              τ = θ + τ0 + (G.cost x y + traversalTime G (y :: w :: rest)) then (1:ℤ) else 0) =
            if 2 ≤ rest.length + 1 + 1 ∧ (y :: w :: rest).getLast? = some z ∧
              τ = θ + (τ0 + G.cost x y) + traversalTime G (y :: w :: rest) then 1 else 0 :=
          if_congr ⟨fun h => ⟨by omega, h.1, by omega⟩, fun h => ⟨h.2.1, by omega⟩⟩ rfl rfl
        rw [c1, c2, c3]; linarith

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

lemma x8_fib (S : Finset (N × N)) (g : N × N → N) (F : N → N × N → ℝ) :
    ∑ x, ∑ q ∈ S.filter (fun q => g q = x), F x q = ∑ q ∈ S, F (g q) q := by
  rw [← Finset.sum_fiberwise S g (fun q => F (g q) q)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun q hq => ?_
  rw [(Finset.mem_filter.mp hq).2]

lemma x8_arcSum_out (G : Network N) (f : N → N → ℝ) (x : N) :
    arcSum G f {x} Finset.univ = ∑ q ∈ G.arcs.filter (fun q => q.1 = x), f q.1 q.2 := by
  simp [arcSum]

lemma x8_arcSum_in (G : Network N) (f : N → N → ℝ) (x : N) :
    arcSum G f Finset.univ {x} = ∑ q ∈ G.arcs.filter (fun q => q.2 = x), f q.1 q.2 := by
  simp [arcSum]

lemma x8_tele (G : Network N) (f : N → N → ℝ) (w : N → ℝ) :
    ∑ q ∈ G.arcs, f q.1 q.2 * (w q.2 - w q.1) = -∑ x, w x * netOut G f x := by
  simp only [netOut, x8_arcSum_out, x8_arcSum_in, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [x8_fib G.arcs Prod.fst (fun x q => w x * f q.1 q.2),
    x8_fib G.arcs Prod.snd (fun x q => w x * f q.1 q.2)]
  rw [neg_sub]
  congr 1 <;> exact Finset.sum_congr rfl fun q _ => by ring

lemma x8_flow_pot (G : Network N) {s t : N} (hst : s ≠ t) {f : N → N → ℝ} {v : ℝ}
    (hf : IsStaticFlow G s t f v) (w : N → ℝ) :
    ∑ q ∈ G.arcs, f q.1 q.2 * (w q.2 - w q.1) = (w t - w s) * v := by
  rw [x8_tele]
  have : ∀ x, w x * netOut G f x =
      (if x = s then w s * v else 0) + (if x = t then -(w t * v) else 0) := by
    intro x
    by_cases hs : x = s
    · subst hs; simp [hst, hf.2.2.1]
    by_cases ht : x = t
    · subst ht; simp [hs, hf.2.2.2.2]
    · simp [hs, ht, hf.2.2.2.1 x hs ht]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma x8_sum_count_filter (S : Finset (N × N)) (Q : N × N → Prop) [DecidablePred Q]
    (L : List (N × N)) (hL : ∀ q ∈ L, q ∈ S) :
    ∑ q ∈ S.filter Q, (L.count q : ℝ) = (L.countP (fun q => Q q) : ℝ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.countP_cons, Nat.cast_add, ← ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    simp only [List.count_cons, Nat.cast_add, Finset.sum_add_distrib]
    congr 1
    by_cases hQ : Q a
    · rw [Finset.sum_eq_single a]
      · simp [hQ]
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_filter.mpr ⟨hL a List.mem_cons_self, hQ⟩) h
    · rw [Finset.sum_eq_zero]
      · simp [hQ]
      · intro b hb
        have : b ≠ a := fun h => hQ (h ▸ (Finset.mem_filter.mp hb).2)
        simp [Ne.symm this]

lemma x8_net_list (z : N) : ∀ l : List N,
    (((x8L l).countP (fun q => q.1 = z) : ℕ) : ℝ) - (((x8L l).countP (fun q => q.2 = z) : ℕ) : ℝ) =
      (if 2 ≤ l.length ∧ l.head? = some z then 1 else 0) -
      (if 2 ≤ l.length ∧ l.getLast? = some z then 1 else 0)
  | [] => by simp
  | [x] => by simp [x8L]
  | x :: y :: rest => by
      have ih := x8_net_list z (y :: rest)
      rw [x8_zip_cons2, List.countP_cons, List.countP_cons]
      have hlast : (x :: y :: rest).getLast? = (y :: rest).getLast? := by
        simp [List.getLast?_cons_cons]
      rw [hlast]
      push_cast
      rcases rest with _ | ⟨w, rest⟩
      · simp [x8L] at ih ⊢
      · simp only [List.length_cons, List.head?_cons, Option.some.injEq, decide_eq_true_eq] at ih ⊢
        have h1 : 2 ≤ rest.length + 1 + 1 := by omega
        have h2 : 2 ≤ rest.length + 1 + 1 + 1 := by omega
        simp only [h1, h2, true_and] at ih ⊢
        linarith

lemma x8_L_nodup : ∀ {l : List N}, l.Nodup → (x8L l).Nodup
  | [], _ => by simp
  | [x], _ => by simp [x8L]
  | x :: y :: rest, h => by
      rw [x8_zip_cons2]
      have h' := (List.nodup_cons.mp h)
      refine List.nodup_cons.mpr ⟨fun hm => h'.1 ?_, x8_L_nodup h'.2⟩
      exact (List.of_mem_zip hm).1

/-- chains of positive arcs: reachability -/
def x8Reach (G : Network N) (f : N → N → ℝ) (s x : N) : Prop :=
  ∃ l : List N, List.IsChain (fun a b => (a, b) ∈ G.arcs ∧ 0 < f a b) l ∧ l.Nodup ∧
    l.head? = some s ∧ l.getLast? = some x

lemma x8_reach_step (G : Network N) (f : N → N → ℝ) {s x y : N} (hx : x8Reach G f s x)
    (hxy : (x, y) ∈ G.arcs) (hf : 0 < f x y) : x8Reach G f s y := by
  obtain ⟨l, hc, hn, hh, hl⟩ := hx
  by_cases hy : y ∈ l
  · obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.mp hy
    refine ⟨l1 ++ [y], ?_, ?_, ?_, List.getLast?_concat⟩
    · have : l1 ++ y :: l2 = (l1 ++ [y]) ++ l2 := by simp
      rw [this] at hc
      exact hc.left_of_append
    · have : l1 ++ y :: l2 = (l1 ++ [y]) ++ l2 := by simp
      rw [this] at hn
      exact hn.sublist (List.sublist_append_left _ _)
    · rcases l1 with _ | ⟨a, l1⟩ <;> simpa using hh
  · refine ⟨l ++ [y], ?_, ?_, ?_, List.getLast?_concat⟩
    · refine hc.append (List.isChain_singleton y) ?_
      intro a ha b hb
      rw [hl] at ha; simp at hb ha; subst ha; subst hb; exact ⟨hxy, hf⟩
    · rw [List.nodup_append]
      refine ⟨hn, List.nodup_singleton y, ?_⟩
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hy ha
    · rcases l with _ | ⟨a, l⟩
      · simp at hh
      · simpa using hh

lemma x8_exists_chain (G : Network N) {s t : N} (hst : s ≠ t) {f : N → N → ℝ} {v : ℝ}
    (hf : IsStaticFlow G s t f v) (hv : 0 < v) :
    ∃ l : List N, IsChainFromTo G s t l ∧ ∀ q ∈ x8L l, 0 < f q.1 q.2 := by
  classical
  have hreach : x8Reach G f s t := by
    by_contra hnt
    let w : N → ℝ := fun x => if x8Reach G f s x then 1 else 0
    have hs : x8Reach G f s s := ⟨[s], by simp, by simp, rfl, rfl⟩
    have key := x8_flow_pot G hst hf w
    have hws : w s = 1 := by simp [w, hs]
    have hwt : w t = 0 := by simp [w, hnt]
    rw [hws, hwt] at key
    have hnn : 0 ≤ ∑ q ∈ G.arcs, f q.1 q.2 * (w q.2 - w q.1) := by
      apply Finset.sum_nonneg
      intro q hq
      rcases (hf.2.1 q hq).1.lt_or_eq with hpos | hzero
      · by_cases h1 : x8Reach G f s q.1
        · have h2 := x8_reach_step G f h1 hq hpos
          simp [w, h1, h2]
        · have : w q.1 = 0 := by simp [w, h1]
          rw [this]
          apply mul_nonneg hpos.le
          simp only [w, sub_zero]; split_ifs <;> norm_num
      · rw [← hzero]; simp
    linarith
  obtain ⟨l, hc, hn, hh, hl⟩ := hreach
  have hlen : 2 ≤ l.length := by
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hh
    · simp at hh hl; exact absurd (hh.symm.trans hl) hst
    · simp
  refine ⟨l, ⟨hlen, hn, hh, hl, fun i h => (List.isChain_iff_getElem.mp hc i h).1⟩, ?_⟩
  intro q hq
  obtain ⟨i, h, rfl⟩ := x8_mem_L hq
  exact (List.isChain_iff_getElem.mp hc i h).2

theorem x8_decomp (G : Network N) {s t : N} (hst : s ≠ t) : ∀ (n : ℕ) (f : N → N → ℝ) (v : ℝ),
    (G.arcs.filter (fun q => 0 < f q.1 q.2)).card = n → IsStaticFlow G s t f v →
    ∃ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro f v hn hf
  by_cases hv : v ≤ 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun r => r.elim0, fun r => r.elim0, by simpa using hv, ?_⟩
    intro q hq; simpa using (hf.2.1 q hq).1
  push Not at hv
  obtain ⟨l, hl, hpos⟩ := x8_exists_chain G hst hf hv
  set L := x8L l with hLdef
  have hLarcs : ∀ q ∈ L, q ∈ G.arcs := fun q hq => x8_L_arcs G hl hq
  have hLnd : L.Nodup := x8_L_nodup hl.2.1
  have hLne : L.toFinset.Nonempty := by
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · have := hl.1; simp at this
    · have := hl.1; simp at this
    · exact ⟨(a, b), by simp [L, x8_zip_cons2]⟩
  obtain ⟨q0, hq0, hmin⟩ := Finset.exists_min_image L.toFinset (fun q => f q.1 q.2) hLne
  rw [List.mem_toFinset] at hq0
  set hh := f q0.1 q0.2 with hhdef
  have hhpos : 0 < hh := hpos q0 hq0
  have hcnt : ∀ q, (L.count q : ℝ) ≤ 1 := by
    intro q
    exact_mod_cast List.nodup_iff_count_le_one.mp hLnd q
  have hle : ∀ q, hh * (L.count q : ℝ) ≤ f q.1 q.2 := by
    intro q
    by_cases hq : q ∈ L
    · rw [List.count_eq_one_of_mem hLnd hq]; simpa using hmin q (List.mem_toFinset.mpr hq)
    · rw [List.count_eq_zero_of_not_mem hq]
      by_cases ha : q ∈ G.arcs
      · simpa using (hf.2.1 q ha).1
      · simp [hf.1 q.1 q.2 ha]
  let f' : N → N → ℝ := fun x y => f x y - hh * (L.count (x, y) : ℝ)
  have hnet : ∀ z, netOut G f' z = netOut G f z -
      hh * ((if z = s then 1 else 0) - (if z = t then 1 else 0)) := by
    intro z
    have e := x8_net_list z l
    simp only [hl.1, true_and, hl.2.2.1, hl.2.2.2.1, Option.some.injEq] at e
    simp only [netOut, x8_arcSum_out, x8_arcSum_in, f', Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [x8_sum_count_filter _ _ L hLarcs, x8_sum_count_filter _ _ L hLarcs]
    have e' : (if s = z then (1:ℝ) else 0) - (if t = z then 1 else 0) =
        (if z = s then 1 else 0) - (if z = t then 1 else 0) := by
      simp only [eq_comm]
    rw [← e', ← e]
    simp only [L]; ring
  have hf' : IsStaticFlow G s t f' (v - hh) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y hxy
      have : (x, y) ∉ L := fun h => hxy (hLarcs _ h)
      simp [f', hf.1 x y hxy, List.count_eq_zero_of_not_mem this]
    · intro q hq
      refine ⟨by simp only [f']; linarith [hle q], ?_⟩
      simp only [f']
      have := (hf.2.1 q hq).2
      have : 0 ≤ hh * (L.count q : ℝ) := mul_nonneg hhpos.le (by positivity)
      linarith
    · rw [hnet, hf.2.2.1]; simp [hst]
    · intro x hxs hxt; rw [hnet, hf.2.2.2.1 x hxs hxt]; simp [hxs, hxt]
    · rw [hnet, hf.2.2.2.2]; simp [Ne.symm hst]; ring
  have hsub : G.arcs.filter (fun q => 0 < f' q.1 q.2) ⊂ G.arcs.filter (fun q => 0 < f q.1 q.2) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨q0, Finset.mem_filter.mpr ⟨hLarcs q0 hq0, hhpos⟩, ?_⟩
      intro hm
      have := (Finset.mem_filter.mp hm).2
      simp only [f', List.count_eq_one_of_mem hLnd hq0] at this
      simp [hhdef] at this
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨hq.1, ?_⟩
      have : 0 ≤ hh * (L.count q : ℝ) := mul_nonneg hhpos.le (by positivity)
      simp only [f'] at hq; linarith [hq.2]
  obtain ⟨m, C, h, hdec⟩ := IH _ (hn ▸ Finset.card_lt_card hsub) f' (v - hh) rfl hf'
  refine ⟨m + 1, Fin.cons l C, Fin.cons hh h, ?_, ?_, ?_, ?_⟩
  · intro r; refine Fin.cases ?_ (fun r => ?_) r
    · simpa using hl
    · simpa using hdec.1 r
  · intro r; refine Fin.cases ?_ (fun r => ?_) r
    · simpa using hhpos
    · simpa using hdec.2.1 r
  · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; linarith [hdec.2.2.1]
  · intro q hq
    rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
    have := hdec.2.2.2 q hq
    simp only [f'] at this
    have e : List.zip l l.tail = L := rfl
    rw [e]; linarith

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

lemma x8_sumcountP (S : Finset (N × N)) (Q : N × N → Prop) [DecidablePred Q]
    (P : N × N → (N × N) × ℕ → Prop) [∀ q, DecidablePred (P q)]
    (E : List ((N × N) × ℕ)) (hE : ∀ e ∈ E, e.1 ∈ S) :
    ∑ q ∈ S.filter Q, (E.countP (fun e => e.1 = q ∧ P q e) : ℝ) =
      (E.countP (fun e => Q e.1 ∧ P e.1 e) : ℝ) := by
  induction E with
  | nil => simp
  | cons a E ih =>
    simp only [List.countP_cons, Nat.cast_add, Finset.sum_add_distrib]
    rw [ih (fun e he => hE e (List.mem_cons_of_mem _ he))]
    congr 1
    by_cases hQ : Q a.1
    · rw [Finset.sum_eq_single a.1]
      · simp [hQ]
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_filter.mpr ⟨hE a List.mem_cons_self, hQ⟩) h
    · rw [Finset.sum_eq_zero]
      · simp [hQ]
      · intro b hb
        have : b ≠ a.1 := fun h => hQ (h ▸ (Finset.mem_filter.mp hb).2)
        simp [Ne.symm this]

lemma x8_timed_arcs (G : Network N) {s t : N} {l : List N} (hl : IsChainFromTo G s t l) (τ0 : ℕ) :
    ∀ e ∈ timedArcs G l τ0, e.1 ∈ G.arcs := by
  intro e he
  apply x8_L_arcs G hl
  rw [← x8_timed_fst G l τ0]
  exact List.mem_map_of_mem he

variable (G : Network N) (p : ℕ) {m : ℕ} (C : Fin m → List N) (h : Fin m → ℝ)

lemma x8_out_rep {s t : N} (hC : ∀ r, IsChainFromTo G s t (C r)) (x : N) (τ : ℕ) :
    outAt G (repeatedFlow G p C h) (fun _ _ => 0) x τ =
      ∑ r, h r * ∑ θ ∈ Finset.range (p + 1), if θ + traversalTime G (C r) ≤ p then
        (((timedArcs G (C r) 0).countP (fun e => e.1.1 = x ∧ θ + e.2 = τ) : ℕ) : ℝ) else 0 := by
  unfold outAt repeatedFlow
  rw [add_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs
  · simp only [← List.countP_eq_length_filter]
    have := x8_sumcountP G.arcs (fun q => q.1 = x) (fun _ e => θ + e.2 = τ)
      (timedArcs G (C r) 0) (x8_timed_arcs G (hC r) 0)
    simpa using this
  · simp

lemma x8_in_rep {s t : N} (hC : ∀ r, IsChainFromTo G s t (C r)) (x : N) (τ : ℕ) :
    inAt G (repeatedFlow G p C h) (fun _ _ => 0) x τ =
      ∑ r, h r * ∑ θ ∈ Finset.range (p + 1), if θ + traversalTime G (C r) ≤ p then
        (((timedArcs G (C r) 0).countP
          (fun e => e.1.2 = x ∧ θ + e.2 + G.cost e.1.1 e.1.2 = τ) : ℕ) : ℝ) else 0 := by
  unfold inAt repeatedFlow
  rw [show (if 1 ≤ τ then (0:ℝ) else 0) = 0 by split_ifs <;> rfl, add_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs
  · simp only [← List.countP_eq_length_filter]
    have := x8_sumcountP G.arcs (fun q => q.2 = x ∧ G.cost q.1 q.2 ≤ τ)
      (fun q e => θ + e.2 = τ - G.cost q.1 q.2)
      (timedArcs G (C r) 0) (x8_timed_arcs G (hC r) 0)
    simp only [Prod.mk.eta] at this ⊢
    rw [this]
    congr 1
    apply List.countP_congr
    intro e _
    simp only [decide_eq_true_eq, and_assoc]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, by omega⟩
    · rintro ⟨a, c⟩; exact ⟨a, by omega, by omega⟩
  · simp

/-- per-copy net outflow, as reals -/
lemma x8_copy_net {s t : N} (hst : s ≠ t) {l : List N} (hl : IsChainFromTo G s t l)
    (θ : ℕ) (z : N) (τ : ℕ) :
    (((timedArcs G l 0).countP (fun e => e.1.1 = z ∧ θ + e.2 = τ) : ℕ) : ℝ) -
      (((timedArcs G l 0).countP
        (fun e => e.1.2 = z ∧ θ + e.2 + G.cost e.1.1 e.1.2 = τ) : ℕ) : ℝ) =
      (if z = s ∧ τ = θ then 1 else 0) - (if z = t ∧ τ = θ + traversalTime G l then 1 else 0) := by
  have e := x8_cons_id G θ z τ l 0
  simp only [hl.1, true_and, hl.2.2.1, hl.2.2.2.1, Option.some.injEq, add_zero] at e
  have e2 : ((((timedArcs G l 0).countP (fun e => e.1.1 = z ∧ θ + e.2 = τ) : ℕ) : ℤ) : ℝ) -
      ((((timedArcs G l 0).countP
        (fun e => e.1.2 = z ∧ θ + e.2 + G.cost e.1.1 e.1.2 = τ) : ℕ) : ℤ) : ℝ) =
      (((if s = z ∧ τ = θ then 1 else 0) - (if t = z ∧ τ = θ + traversalTime G l then 1 else 0) : ℤ) : ℝ) := by
    rw [← e]; push_cast; ring
  simp only [Int.cast_natCast] at e2
  rw [e2]
  push_cast
  simp only [eq_comm (a := s), eq_comm (a := t)]

lemma x8_net_rep {s t : N} (hst : s ≠ t) (hC : ∀ r, IsChainFromTo G s t (C r)) (z : N) (τ : ℕ) :
    outAt G (repeatedFlow G p C h) (fun _ _ => 0) z τ - inAt G (repeatedFlow G p C h) (fun _ _ => 0) z τ =
      ∑ r, h r * ∑ θ ∈ Finset.range (p + 1), if θ + traversalTime G (C r) ≤ p then
        ((if z = s ∧ τ = θ then 1 else 0) -
          (if z = t ∧ τ = θ + traversalTime G (C r) then 1 else 0)) else 0 := by
  rw [x8_out_rep G p C h hC, x8_in_rep G p C h hC, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun θ _ => ?_
  by_cases h1 : θ + traversalTime G (C r) ≤ p
  · simp only [if_pos h1]; exact x8_copy_net G hst (hC r) θ z τ
  · simp only [if_neg h1]; simp

lemma x8_cnt_bound (q : N × N) (τ : ℕ) : ∀ (E : List ((N × N) × ℕ)) (n : ℕ),
    ∑ θ ∈ Finset.range n, E.countP (fun e => e.1 = q ∧ θ + e.2 = τ) ≤ E.countP (fun e => e.1 = q)
  | [], n => by simp
  | e :: E, n => by
      simp only [List.countP_cons, Finset.sum_add_distrib]
      refine add_le_add (x8_cnt_bound q τ E n) ?_
      by_cases he : e.1 = q
      · simp only [he, true_and, decide_true, if_true]
        rw [Finset.sum_boole]
        simp only [decide_eq_true_eq, Nat.cast_id]
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp at ha hb; omega
      · simp [he]

lemma x8_rep_le {s t : N} {f : N → N → ℝ} {v : ℝ} (hdec : IsChainDecomposition G s t f v C h)
    (q : N × N) (hq : q ∈ G.arcs) (τ : ℕ) :
    0 ≤ repeatedFlow G p C h q.1 q.2 τ ∧ repeatedFlow G p C h q.1 q.2 τ ≤ f q.1 q.2 := by
  constructor
  · unfold repeatedFlow
    refine Finset.sum_nonneg fun r _ => mul_nonneg (hdec.2.1 r).le ?_
    refine Finset.sum_nonneg fun θ _ => ?_
    split_ifs <;> positivity
  · refine le_trans ?_ (hdec.2.2.2 q hq)
    unfold repeatedFlow
    refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hdec.2.1 r).le
    have hc : (List.zip (C r) (C r).tail).count q =
        (timedArcs G (C r) 0).countP (fun e => e.1 = q) := by
      show List.count q (x8L (C r)) = _
      rw [← x8_timed_fst G (C r) 0, List.count_eq_countP, List.countP_map]
      apply List.countP_congr; intro e _; simp
    rw [hc]
    have := x8_cnt_bound q τ (timedArcs G (C r) 0) (p + 1)
    calc (∑ θ ∈ Finset.range (p + 1), if θ + traversalTime G (C r) ≤ p then
          ((List.filter (fun e => decide (e.1 = (q.1, q.2) ∧ θ + e.2 = τ))
            (timedArcs G (C r) 0)).length : ℝ) else 0)
        ≤ ∑ θ ∈ Finset.range (p + 1),
          (((timedArcs G (C r) 0).countP (fun e => e.1 = q ∧ θ + e.2 = τ) : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun θ _ => ?_
          split_ifs
          · simp [List.countP_eq_length_filter]
          · positivity
      _ ≤ _ := by exact_mod_cast this

/-- the value of the repeated flow -/
noncomputable def x8V : ℝ :=
  ∑ r, h r * ∑ θ ∈ Finset.range (p + 1), if θ + traversalTime G (C r) ≤ p then (1:ℝ) else 0

lemma x8_rep_dyn {s t : N} (hst : s ≠ t) {f : N → N → ℝ} {v : ℝ}
    (hdec : IsChainDecomposition G s t f v C h) (hf : IsStaticFlow G s t f v) :
    IsDynamicFlow G s t p (repeatedFlow G p C h) (fun _ _ => 0) (x8V G p C h) := by
  have hC := hdec.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [x8_net_rep G p C h hst hC]
    rw [Finset.sum_comm, x8V, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [← Finset.mul_sum, ← mul_sub, Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun θ hθ => ?_)
    split_ifs with h1
    · simp only [true_and, hst, false_and, if_false, sub_zero]
      rw [Finset.sum_ite_eq', if_pos hθ]; ring
    · simp
  · intro x hxs hxt τ _
    rw [x8_net_rep G p C h hst hC]
    simp [hxs, hxt]
  · simp only [x8_net_rep G p C h hst hC]
    rw [Finset.sum_comm, x8V, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [← Finset.mul_sum, ← mul_add, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun θ hθ => ?_)
    split_ifs with h1
    · simp only [true_and, hst.symm, false_and, if_false, zero_sub]
      rw [Finset.sum_neg_distrib, Finset.sum_ite_eq', if_pos (by simp; omega)]; ring
    · simp
  · intro q hq τ _
    exact ⟨(x8_rep_le G p C h hdec q hq τ).1,
      (x8_rep_le G p C h hdec q hq τ).2.trans (hf.2.1 q hq).2⟩
  · intro x τ _; exact le_refl 0

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

lemma x8_V_eq (G : Network N) {s t : N} (hst : s ≠ t) (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2)
    (p : ℕ) {f : N → N → ℝ} {v : ℝ} (hf : IsStaticFlow G s t f v) {π : N → ℤ}
    (hπ : OptimalityProperties G s t (p + 1) f π)
    {m : ℕ} {C : Fin m → List N} {h : Fin m → ℝ} (hdec : IsChainDecomposition G s t f v C h) :
    x8V G p C h = ((p : ℝ) + 1) * v - totalCost G f := by
  set Δ : N × N → ℝ := fun q => (π q.2 : ℝ) - π q.1 with hΔ
  have hle : ∀ q ∈ G.arcs, 0 < f q.1 q.2 → (G.cost q.1 q.2 : ℝ) ≤ Δ q := by
    intro q hq hpos
    have h1 := (hπ.2.2 q hq).1
    have : ¬ (π q.2 - π q.1 < (G.cost q.1 q.2 : ℤ)) := fun hc => by linarith [h1 hc]
    push Not at this
    simp only [hΔ]; exact_mod_cast this
  set g : N × N → ℝ := fun q => ∑ r, h r * ((x8L (C r)).count q : ℝ) with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    Finset.sum_nonneg fun r _ => mul_nonneg (hdec.2.1 r).le (by positivity)
  have hgf : ∀ q ∈ G.arcs, g q ≤ f q.1 q.2 := fun q hq => hdec.2.2.2 q hq
  have hchain : ∀ r, ((x8L (C r)).map Δ).sum = (p : ℝ) + 1 := by
    intro r
    have := x8_tele_list (fun x => (π x : ℝ)) (C r) s t (hdec.1 r).2.2.1 (hdec.1 r).2.2.2.1
    rw [show Δ = fun q => (π q.2 : ℝ) - π q.1 from rfl, this, hπ.1, hπ.2.1]; push_cast; ring
  have hsumL : ∀ (F : N × N → ℝ), ∑ q ∈ G.arcs, g q * F q = ∑ r, h r * ((x8L (C r)).map F).sum := by
    intro F
    simp only [hg, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← x8_sum_count G.arcs F (x8L (C r)) (fun q hq => x8_L_arcs G (hdec.1 r) hq), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [nsmul_eq_mul]; ring
  have hgΔ : ∑ q ∈ G.arcs, g q * Δ q = ((p : ℝ) + 1) * ∑ r, h r := by
    rw [hsumL, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [hchain]; ring
  have hfΔ : ∑ q ∈ G.arcs, f q.1 q.2 * Δ q = ((p : ℝ) + 1) * v := by
    have := x8_flow_pot G hst hf (fun x => (π x : ℝ))
    rw [show (fun q : N × N => f q.1 q.2 * Δ q) = fun q => f q.1 q.2 * ((π q.2 : ℝ) - π q.1) from rfl,
      this, hπ.1, hπ.2.1]; push_cast; ring
  have hd1 : ∑ q ∈ G.arcs, (f q.1 q.2 - g q) * (G.cost q.1 q.2 : ℝ) ≤
      ∑ q ∈ G.arcs, (f q.1 q.2 - g q) * Δ q := by
    refine Finset.sum_le_sum fun q hq => ?_
    rcases (sub_nonneg.mpr (hgf q hq)).lt_or_eq with hlt | heq
    · exact mul_le_mul_of_nonneg_left (hle q hq (by linarith [hg0 q])) hlt.le
    · rw [← heq]; simp
  have hd2 : 0 ≤ ∑ q ∈ G.arcs, (f q.1 q.2 - g q) * (G.cost q.1 q.2 : ℝ) :=
    Finset.sum_nonneg fun q hq => mul_nonneg (sub_nonneg.mpr (hgf q hq)) (by positivity)
  have hd3 : ∑ q ∈ G.arcs, (f q.1 q.2 - g q) * Δ q = ((p : ℝ) + 1) * (v - ∑ r, h r) := by
    simp only [sub_mul, Finset.sum_sub_distrib]; rw [hfΔ, hgΔ]; ring
  have hH : ∑ r, h r = v := by
    have h3 := hdec.2.2.1
    have : 0 ≤ ((p : ℝ) + 1) * (v - ∑ r, h r) := by linarith
    have hp : (0:ℝ) < (p : ℝ) + 1 := by positivity
    have := (mul_nonneg_iff_of_pos_left hp).mp this
    linarith
  have hcostEq : ∑ q ∈ G.arcs, g q * (G.cost q.1 q.2 : ℝ) = totalCost G f := by
    have : ∑ q ∈ G.arcs, (f q.1 q.2 - g q) * (G.cost q.1 q.2 : ℝ) = 0 := by
      rw [hd3, hH, sub_self, mul_zero] at hd1; linarith
    simp only [sub_mul, Finset.sum_sub_distrib] at this
    unfold totalCost
    rw [show ∑ q ∈ G.arcs, (G.cost q.1 q.2 : ℝ) * f q.1 q.2 = ∑ q ∈ G.arcs, f q.1 q.2 * G.cost q.1 q.2
      from Finset.sum_congr rfl fun q _ => mul_comm _ _]
    linarith
  have hσ : ∀ r, (traversalTime G (C r) : ℝ) = ((x8L (C r)).map (fun q => (G.cost q.1 q.2 : ℝ))).sum := by
    intro r
    rw [x8_traversal, Nat.cast_list_sum, List.map_map]; rfl
  have hσle : ∀ r, traversalTime G (C r) ≤ p + 1 := by
    intro r
    have : (traversalTime G (C r) : ℝ) ≤ (p : ℝ) + 1 := by
      rw [hσ, ← hchain r]
      apply List.sum_le_sum
      intro q hq
      have hqa := x8_L_arcs G (hdec.1 r) hq
      apply hle q hqa
      have hc1 : (1:ℝ) ≤ ((x8L (C r)).count q : ℝ) := by
        exact_mod_cast List.count_pos_iff.mpr hq
      have : h r * ((x8L (C r)).count q : ℝ) ≤ g q :=
        Finset.single_le_sum (f := fun r => h r * ((x8L (C r)).count q : ℝ))
          (fun r _ => mul_nonneg (hdec.2.1 r).le (by positivity)) (Finset.mem_univ r)
      nlinarith [hdec.2.1 r, hgf q hqa]
    exact_mod_cast this
  have hcard : ∀ r, (∑ θ ∈ Finset.range (p + 1),
      if θ + traversalTime G (C r) ≤ p then (1:ℝ) else 0) = (p : ℝ) + 1 - traversalTime G (C r) := by
    intro r
    rw [Finset.sum_boole]
    have : (Finset.range (p + 1)).filter (fun θ => θ + traversalTime G (C r) ≤ p) =
        Finset.range (p + 1 - traversalTime G (C r)) := by
      ext θ; simp; omega
    rw [this, Finset.card_range, Nat.cast_sub (hσle r)]; push_cast; ring
  unfold x8V
  simp only [hcard]
  rw [← hcostEq, hsumL]
  simp only [← hσ, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hH]; ring

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

lemma x8_shift (a p : ℕ) (F : ℕ → ℝ) :
    ∑ τ ∈ Finset.range (p + 1), (if a ≤ τ then F τ else 0) =
      ∑ σ ∈ Finset.range (p + 1), (if σ + a ≤ p then F (σ + a) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun τ => τ - a) (fun σ => σ + a)
  · intro τ hτ; simp at hτ ⊢; omega
  · intro σ hσ; simp at hσ ⊢; omega
  · intro τ hτ; simp at hτ ⊢; omega
  · intro σ hσ; simp
  · intro τ hτ; simp at hτ; congr 1; omega

lemma x8_expand (G : Network N) (p : ℕ) (f : N → N → ℕ → ℝ) (hold : N → ℕ → ℝ)
    (w : N → ℕ → ℝ) :
    ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * (outAt G f hold x τ - inAt G f hold x τ) =
      ∑ q ∈ G.arcs, ∑ τ ∈ Finset.range (p + 1), f q.1 q.2 τ *
          (w q.1 τ - if τ + G.cost q.1 q.2 ≤ p then w q.2 (τ + G.cost q.1 q.2) else 0) +
      ∑ x, ∑ τ ∈ Finset.range (p + 1), hold x τ * (w x τ - if τ + 1 ≤ p then w x (τ + 1) else 0) := by
  have hout : ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * outAt G f hold x τ =
      ∑ q ∈ G.arcs, ∑ τ ∈ Finset.range (p + 1), f q.1 q.2 τ * w q.1 τ +
      ∑ x, ∑ τ ∈ Finset.range (p + 1), hold x τ * w x τ := by
    simp only [outAt, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [← x8_fib G.arcs Prod.fst (fun x q => ∑ τ ∈ Finset.range (p + 1), f q.1 q.2 τ * w x τ)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun τ _ => by ring
    · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun τ _ => by ring
  have hin : ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * inAt G f hold x τ =
      ∑ q ∈ G.arcs, ∑ τ ∈ Finset.range (p + 1), f q.1 q.2 τ *
          (if τ + G.cost q.1 q.2 ≤ p then w q.2 (τ + G.cost q.1 q.2) else 0) +
      ∑ x, ∑ τ ∈ Finset.range (p + 1), hold x τ * (if τ + 1 ≤ p then w x (τ + 1) else 0) := by
    simp only [inAt, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · have e1 : ∀ x τ, ∑ q ∈ G.arcs.filter (fun q => q.2 = x ∧ G.cost q.1 q.2 ≤ τ),
          w x τ * f q.1 q.2 (τ - G.cost q.1 q.2) =
          ∑ q ∈ G.arcs.filter (fun q => q.2 = x),
            (if G.cost q.1 q.2 ≤ τ then w x τ * f q.1 q.2 (τ - G.cost q.1 q.2) else 0) := by
        intro x τ
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
      simp only [e1]
      trans ∑ x, ∑ q ∈ G.arcs.filter (fun q => q.2 = x), ∑ τ ∈ Finset.range (p + 1),
        (if G.cost q.1 q.2 ≤ τ then w x τ * f q.1 q.2 (τ - G.cost q.1 q.2) else 0)
      · exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
      rw [x8_fib G.arcs Prod.snd (fun x q => ∑ τ ∈ Finset.range (p + 1),
        (if G.cost q.1 q.2 ≤ τ then w x τ * f q.1 q.2 (τ - G.cost q.1 q.2) else 0))]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [x8_shift (G.cost q.1 q.2) p (fun τ => w q.2 τ * f q.1 q.2 (τ - G.cost q.1 q.2))]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs <;> simp [mul_comm]
    · refine Finset.sum_congr rfl fun x _ => ?_
      have := x8_shift 1 p (fun τ => w x τ * hold x (τ - 1))
      simp only [mul_ite, mul_zero] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs <;> simp [mul_comm]
  have hsplit : ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * (outAt G f hold x τ - inAt G f hold x τ) =
      ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * outAt G f hold x τ -
      ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * inAt G f hold x τ := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit, hout, hin]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma x8_weak (G : Network N) {s t : N} (hst : s ≠ t) (p : ℕ) {f : N → N → ℕ → ℝ}
    {hold : N → ℕ → ℝ} {v : ℝ} (hd : IsDynamicFlow G s t p f hold v)
    {Y : Finset (N × ℕ)} (hY : IsDynamicCut s t p Y) (hYh : ¬ HoldoverCrosses p Y) :
    v ≤ dynamicCutCapacity G p Y := by
  have hsum : ∀ w : N → ℕ → ℝ, (∀ τ ≤ p, w s τ = 1) → (∀ τ ≤ p, w t τ = 0) →
      ∑ x, ∑ τ ∈ Finset.range (p + 1), w x τ * (outAt G f hold x τ - inAt G f hold x τ) = v := by
    intro w hs ht
    have : ∀ x, ∑ τ ∈ Finset.range (p + 1), w x τ * (outAt G f hold x τ - inAt G f hold x τ) =
        if x = s then v else 0 := by
      intro x
      by_cases hxs : x = s
      · subst hxs
        rw [if_pos rfl, ← sub_eq_zero, ← hd.1]
        congr 1
        refine Finset.sum_congr rfl fun τ hτ => ?_
        rw [hs τ (by simp at hτ; omega), one_mul]
      by_cases hxt : x = t
      · subst hxt
        rw [if_neg hxs]
        exact Finset.sum_eq_zero fun τ hτ => by rw [ht τ (by simp at hτ; omega), zero_mul]
      · rw [if_neg hxs]
        exact Finset.sum_eq_zero fun τ hτ => by
          rw [hd.2.1 x hxs hxt τ (by simp at hτ; omega), mul_zero]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  classical
  let wY : N → ℕ → ℝ := fun x τ => if (x, τ) ∈ Y then 1 else 0
  have h1 := hsum wY (fun τ hτ => by simp [wY, (hY τ hτ).1]) (fun τ hτ => by simp [wY, (hY τ hτ).2])
  have h0 : ∑ x, ∑ τ ∈ Finset.range (p + 1), (fun _ _ => (1:ℝ)) x τ *
      (outAt G f hold x τ - inAt G f hold x τ) = 0 := by
    have : ∀ x, ∑ τ ∈ Finset.range (p + 1), (fun _ _ => (1:ℝ)) x τ *
        (outAt G f hold x τ - inAt G f hold x τ) =
        (if x = s then v else 0) + (if x = t then -v else 0) := by
      intro x
      simp only [one_mul]
      by_cases hxs : x = s
      · subst hxs; rw [if_pos rfl, if_neg hst]; linarith [hd.1]
      by_cases hxt : x = t
      · subst hxt; rw [if_neg hxs, if_pos rfl]; linarith [hd.2.2.1]
      · rw [if_neg hxs, if_neg hxt]
        exact (Finset.sum_eq_zero fun τ hτ => hd.2.1 x hxs hxt τ (by simp at hτ; omega)).trans
          (by ring)
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [x8_expand] at h1 h0
  have hA : ∀ q ∈ G.arcs, ∀ τ ∈ Finset.range (p + 1), f q.1 q.2 τ *
      (wY q.1 τ - if τ + G.cost q.1 q.2 ≤ p then wY q.2 (τ + G.cost q.1 q.2) else 0) ≤
      (if τ + G.cost q.1 q.2 ≤ p ∧ (q.1, τ) ∈ Y ∧ (q.2, τ + G.cost q.1 q.2) ∉ Y then
        (G.cap q.1 q.2 : ℝ) else 0) +
      f q.1 q.2 τ * ((fun _ _ => (1:ℝ)) q.1 τ -
        if τ + G.cost q.1 q.2 ≤ p then (fun _ _ => (1:ℝ)) q.2 (τ + G.cost q.1 q.2) else 0) := by
    intro q hq τ hτ
    obtain ⟨f0, fc⟩ := hd.2.2.2.1 q hq τ (by simp at hτ; omega)
    by_cases ha : τ + G.cost q.1 q.2 ≤ p <;> by_cases hb : (q.1, τ) ∈ Y <;>
      by_cases hc : (q.2, τ + G.cost q.1 q.2) ∈ Y <;> simp [wY, ha, hb, hc] <;> linarith
  have hB : ∀ x, ∀ τ ∈ Finset.range (p + 1), hold x τ *
      (wY x τ - if τ + 1 ≤ p then wY x (τ + 1) else 0) ≤
      hold x τ * ((fun _ _ => (1:ℝ)) x τ - if τ + 1 ≤ p then (fun _ _ => (1:ℝ)) x (τ + 1) else 0) := by
    intro x τ hτ
    have h0 := hd.2.2.2.2 x τ (by simp at hτ; omega)
    apply mul_le_mul_of_nonneg_left _ h0
    by_cases ha : τ + 1 ≤ p
    · have : (x, τ) ∈ Y → (x, τ + 1) ∈ Y := by
        intro hx; by_contra hn; exact hYh ⟨x, τ, by omega, hx, hn⟩
      by_cases hb : (x, τ) ∈ Y
      · simp [wY, ha, hb, this hb]
      · simp only [wY, ha, hb, if_true, if_false]; split_ifs <;> norm_num
    · simp only [wY, ha, if_false]; split_ifs <;> norm_num
  have hAs := Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun τ hτ => hA q hq τ hτ
  have hBs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum fun τ hτ => hB x τ hτ
  simp only [Finset.sum_add_distrib] at hAs
  unfold dynamicCutCapacity
  linarith

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

variable {N : Type} [Fintype N] [DecidableEq N]

lemma x8_mem_nnc (π : N → ℤ) (p : ℕ) (x : N) (τ : ℕ) :
    (x, τ) ∈ nodeNumberCut π p ↔ τ < p + 1 ∧ π x ≤ (τ : ℤ) := by
  simp [nodeNumberCut]

lemma x8_cut_ok {s t : N} (π : N → ℤ) (p : ℕ) (hs : π s = 0) (ht : π t = (p + 1 : ℕ)) :
    IsDynamicCut s t p (nodeNumberCut π p) ∧ ¬ HoldoverCrosses p (nodeNumberCut π p) := by
  refine ⟨fun τ hτ => ⟨?_, ?_⟩, ?_⟩
  · rw [x8_mem_nnc, hs]; exact ⟨by omega, by positivity⟩
  · rw [x8_mem_nnc, ht]; push_cast; omega
  · rintro ⟨x, τ, hτ, h1, h2⟩
    rw [x8_mem_nnc] at h1 h2
    exact h2 ⟨by omega, by push_cast; omega⟩

lemma x8_cut_cap (G : Network N) {s t : N} (hst : s ≠ t) (p : ℕ) {f : N → N → ℝ} {v : ℝ}
    (hf : IsStaticFlow G s t f v) {π : N → ℤ} (hπ : OptimalityProperties G s t (p + 1) f π) :
    dynamicCutCapacity G p (nodeNumberCut π p) ≤ ((p : ℝ) + 1) * v - totalCost G f := by
  have hpot := x8_flow_pot G hst hf (fun x => (π x : ℝ))
  rw [hπ.1, hπ.2.1] at hpot
  have key : ∀ q ∈ G.arcs, (∑ τ ∈ Finset.range (p + 1),
      if τ + G.cost q.1 q.2 ≤ p ∧ (q.1, τ) ∈ nodeNumberCut π p ∧
        (q.2, τ + G.cost q.1 q.2) ∉ nodeNumberCut π p then (G.cap q.1 q.2 : ℝ) else 0) ≤
      f q.1 q.2 * (((π q.2 : ℝ) - π q.1) - G.cost q.1 q.2) := by
    intro q hq
    obtain ⟨hlt, hgt⟩ := hπ.2.2 q hq
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    set S := (Finset.range (p + 1)).filter (fun τ => τ + G.cost q.1 q.2 ≤ p ∧
      (q.1, τ) ∈ nodeNumberCut π p ∧ (q.2, τ + G.cost q.1 q.2) ∉ nodeNumberCut π p)
    have hS : ∀ τ ∈ S, π q.1 ≤ (τ : ℤ) ∧ (τ : ℤ) < π q.2 - G.cost q.1 q.2 := by
      intro τ hτ
      simp only [S, Finset.mem_filter, x8_mem_nnc] at hτ
      refine ⟨hτ.2.2.1.2, ?_⟩
      by_contra hc
      exact hτ.2.2.2 ⟨by omega, by push_cast; omega⟩
    rcases lt_trichotomy (π q.2 - π q.1) (G.cost q.1 q.2 : ℤ) with h1 | h1 | h1
    · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun τ hτ => by
        have := hS τ hτ; omega
      rw [hS0, hlt h1]; simp
    · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun τ hτ => by
        have := hS τ hτ; omega
      have : ((π q.2 : ℝ) - π q.1) - G.cost q.1 q.2 = 0 := by
        have : ((π q.2 - π q.1 : ℤ) : ℝ) = (G.cost q.1 q.2 : ℤ) := by rw [h1]
        push_cast at this; linarith
      rw [hS0, this]; simp
    · rw [hgt h1]
      have hcard : (S.card : ℤ) ≤ π q.2 - π q.1 - G.cost q.1 q.2 := by
        have : S.card ≤ (Finset.Ico (π q.1) (π q.2 - G.cost q.1 q.2)).card := by
          refine Finset.card_le_card_of_injOn (fun τ : ℕ => (τ : ℤ)) ?_ ?_
          · intro τ hτ
            have := hS τ hτ
            simp only [Finset.coe_Ico, Set.mem_Ico]; exact this
          · intro a _ b _ hab; simpa using hab
        rw [Int.card_Ico] at this
        have h2 := Int.toNat_of_nonneg (show 0 ≤ π q.2 - G.cost q.1 q.2 - π q.1 by omega)
        omega
      have hcard' : (S.card : ℝ) ≤ ((π q.2 : ℝ) - π q.1) - G.cost q.1 q.2 := by
        have : ((S.card : ℤ) : ℝ) ≤ ((π q.2 - π q.1 - G.cost q.1 q.2 : ℤ) : ℝ) := by
          exact_mod_cast hcard
        push_cast at this; linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcard' (by positivity)
  unfold dynamicCutCapacity
  calc _ ≤ ∑ q ∈ G.arcs, f q.1 q.2 * (((π q.2 : ℝ) - π q.1) - G.cost q.1 q.2) :=
        Finset.sum_le_sum key
    _ = _ := by
      unfold totalCost
      rw [show (∑ q ∈ G.arcs, f q.1 q.2 * (((π q.2 : ℝ) - π q.1) - G.cost q.1 q.2)) =
          ∑ q ∈ G.arcs, f q.1 q.2 * ((π q.2 : ℝ) - π q.1) -
            ∑ q ∈ G.arcs, (G.cost q.1 q.2 : ℝ) * f q.1 q.2 by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun q _ => by ring, hpot]
      push_cast; ring

theorem x8_main {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π) :
    (∃ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h) ∧
    (∀ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h →
      IsMaximalDynamicFlow G s t p (repeatedFlow G p C h) (fun _ _ => 0)
        (((p : ℝ) + 1) * v - totalCost G f)) ∧
    IsMinimalDynamicCut G s t p (nodeNumberCut π p) := by
  have hex := x8_decomp G hst _ f v rfl hf
  have hcut := x8_cut_ok (s := s) (t := t) π p hπ.1 (by rw [hπ.2.1])
  have hcap := x8_cut_cap G hst p hf hπ
  have hdyn : ∀ (m : ℕ) (C : Fin m → List N) (h : Fin m → ℝ), IsChainDecomposition G s t f v C h →
      IsDynamicFlow G s t p (repeatedFlow G p C h) (fun _ _ => 0)
        (((p : ℝ) + 1) * v - totalCost G f) := by
    intro m C h hdec
    rw [← x8_V_eq G hst hcost p hf hπ hdec]
    exact x8_rep_dyn G p C h hst hdec hf
  refine ⟨hex, fun m C h hdec => ⟨hdyn m C h hdec, fun f' hold' v' hd => ?_⟩, hcut.1, hcut.2, ?_⟩
  · exact (x8_weak G hst p hd hcut.1 hcut.2).trans hcap
  · intro Y hY hYh
    obtain ⟨m, C, h, hdec⟩ := hex
    exact hcap.trans (x8_weak G hst p (hdyn m C h hdec) hY hYh)

end FlowsNetworks.DynamicFlow


namespace FlowsNetworks.DynamicFlow

lemma x8_greatest {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π) :
    IsGreatest (dynamicFlowValues G s t p) (((p : ℝ) + 1) * v - totalCost G f) := by
  obtain ⟨⟨m, C, h, hdec⟩, h2, _⟩ := x8_main G s t hst hcost p f v hf hint π hπ
  obtain ⟨hd, hmax⟩ := h2 m C h hdec
  exact ⟨⟨_, _, hd⟩, fun v' ⟨f', hold', hd'⟩ => hmax f' hold' v' hd'⟩

theorem x8_incr {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ) (hp : 1 ≤ p)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π π' : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π)
    (hπ' : OptimalityProperties G s t p f π') :
    ∃ V V' : ℝ, IsGreatest (dynamicFlowValues G s t p) V ∧
      IsGreatest (dynamicFlowValues G s t (p - 1)) V' ∧ V - V' = v := by
  have hp' : p - 1 + 1 = p := by omega
  rw [← hp'] at hπ'
  refine ⟨_, _, x8_greatest G s t hst hcost p f v hf hint π hπ,
    x8_greatest G s t hst hcost (p - 1) f v hf hint π' hπ', ?_⟩
  rw [Nat.cast_sub hp]; push_cast; ring

end FlowsNetworks.DynamicFlow

open FlowsNetworks.DynamicFlow in
theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hcost : ∀ q ∈ G.arcs, 0 < G.cost q.1 q.2) (p : ℕ) (hp : 1 ≤ p)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π π' : N → ℤ) (hπ : OptimalityProperties G s t (p + 1) f π)
    (hπ' : OptimalityProperties G s t p f π') :
    ∃ V V' : ℝ, IsGreatest (dynamicFlowValues G s t p) V ∧
      IsGreatest (dynamicFlowValues G s t (p - 1)) V' ∧ V - V' = v :=
  x8_incr G s t hst hcost p hp f v hf hint π π' hπ hπ'
