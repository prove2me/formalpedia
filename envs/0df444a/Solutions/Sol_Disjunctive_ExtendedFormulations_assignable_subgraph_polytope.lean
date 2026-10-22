-- Prove2me | solution 1 for Disjunctive.ExtendedFormulations.assignable_subgraph_polytope
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:17:50.137039+00:00
-- url     : https://prove2.me/submissions/e82f8d07-fd7c-4b7a-b717-2038231f29df

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic



namespace Disjunctive.ExtendedFormulations

open Finset Filter Topology

section
variable {V : Type*} [Fintype V] [DecidableEq V]

def bpLd (y : V → V → ℝ) (a : V) : ℝ := ∑ b, y a b + ∑ b, y b a

def bpTot (y : V → V → ℝ) : ℝ := ∑ a, ∑ b, y a b

def bpE (v w : V) : V → V → ℝ := fun p q => if p = v ∧ q = w then 1 else 0

lemma bpLd_add (y d : V → V → ℝ) (c : ℝ) (a : V) :
    bpLd (fun p q => y p q + c * d p q) a = bpLd y a + c * bpLd d a := by
  simp only [bpLd, Finset.sum_add_distrib, Finset.mul_sum, mul_add]; ring

lemma bpTot_add (y d : V → V → ℝ) (c : ℝ) :
    bpTot (fun p q => y p q + c * d p q) = bpTot y + c * bpTot d := by
  simp only [bpTot, Finset.sum_add_distrib, Finset.mul_sum]

lemma bpLd_E (v w a : V) :
    bpLd (bpE v w) a = (if a = v then 1 else 0) + (if a = w then 1 else 0) := by
  simp only [bpLd, bpE]
  congr 1
  · by_cases h : a = v
    · simp [h]
    · simp [h]
  · by_cases h : a = w
    · simp [h]
    · simp [h]

end

section
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (part : V → Bool)

def bpStep (y : V → V → ℝ) (u v : V) : Prop :=
  (part u = true ∧ G.Adj u v) ∨ (part u = false ∧ 0 < y v u)

lemma bpTot_eq_T (hBip : ∀ i j, G.Adj i j → part i ≠ part j) (d : V → V → ℝ)
    (hd : ∀ a b, d a b ≠ 0 → G.Adj a b ∧ part a = true) :
    bpTot d = ∑ a ∈ univ.filter (fun i => part i = true), bpLd d a := by
  rw [Finset.sum_filter]
  unfold bpTot
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with ha
  · have : ∑ b, d b a = 0 := by
      refine Finset.sum_eq_zero (fun b _ => ?_)
      by_contra h
      have h1 := hd b a h
      have := hBip b a h1.1
      rw [h1.2, ha] at this; exact this rfl
    simp [bpLd, this]
  · refine Finset.sum_eq_zero (fun b _ => ?_)
    by_contra h
    exact ha (hd a b h).2

lemma bpTot_eq_F (hBip : ∀ i j, G.Adj i j → part i ≠ part j) (d : V → V → ℝ)
    (hd : ∀ a b, d a b ≠ 0 → G.Adj a b ∧ part a = true) :
    bpTot d = ∑ a ∈ univ.filter (fun i => part i = false), bpLd d a := by
  rw [Finset.sum_filter]
  unfold bpTot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with ha
  · have : ∑ b, d a b = 0 := by
      refine Finset.sum_eq_zero (fun b _ => ?_)
      by_contra h
      have h1 := hd a b h
      rw [ha] at h1; exact Bool.false_ne_true h1.2
    simp [bpLd, this]
  · refine Finset.sum_eq_zero (fun b _ => ?_)
    by_contra h
    have h1 := hd b a h
    have := hBip b a h1.1
    rw [h1.2] at this
    cases hp : part a <;> simp_all

lemma bp_augment (hBip : ∀ i j, G.Adj i j → part i ≠ part j) (y : V → V → ℝ)
    (hy : ∀ a b, y a b ≠ 0 → G.Adj a b ∧ part a = true) (i0 : V) (hi0 : part i0 = true)
    (v : V) (hv : Relation.ReflTransGen (bpStep G part y) i0 v) :
    ∃ d : V → V → ℝ, (∀ a b, d a b ≠ 0 → G.Adj a b ∧ part a = true) ∧
      (∀ a b, d a b < 0 → 0 < y a b) ∧
      ∀ a, bpLd d a = (if a = i0 then 1 else 0) +
        (if a = v then (if part v = true then -1 else 1) else 0) := by
  induction hv with
  | refl =>
    refine ⟨fun _ _ => 0, by simp, by simp, fun a => ?_⟩
    simp only [bpLd, Finset.sum_const_zero, add_zero, hi0]
    split_ifs <;> norm_num
  | @tail b c _ hst ih =>
    obtain ⟨d, hd1, hd2, hd3⟩ := ih
    rcases hst with ⟨hb, hadj⟩ | ⟨hb, hpos⟩
    · have hc : part c = false := by
        have := hBip b c hadj; rw [hb] at this; simpa using this
      have hbc : b ≠ c := hadj.ne
      refine ⟨fun p q => d p q + 1 * bpE b c p q, ?_, ?_, ?_⟩
      · intro p q hne
        by_cases h : p = b ∧ q = c
        · obtain ⟨rfl, rfl⟩ := h; exact ⟨hadj, hb⟩
        · simp only [bpE, h, if_false, mul_zero, add_zero] at hne
          exact hd1 p q hne
      · intro p q hneg
        by_cases h : p = b ∧ q = c
        · obtain ⟨rfl, rfl⟩ := h
          simp only [bpE, and_self, if_true, mul_one] at hneg
          exact hd2 _ _ (by linarith)
        · simp only [bpE, h, if_false, mul_zero, add_zero] at hneg
          exact hd2 p q hneg
      · intro a
        rw [bpLd_add, bpLd_E, hd3, hb, hc]
        by_cases hab : a = b
        · subst hab; simp [hbc]
        · by_cases hac : a = c
          · subst hac; simp [hab]
          · simp [hab, hac]
    · have hyc := hy c b hpos.ne'
      have hc : part c = true := hyc.2
      have hbc : b ≠ c := hyc.1.ne.symm
      refine ⟨fun p q => d p q + (-1) * bpE c b p q, ?_, ?_, ?_⟩
      · intro p q hne
        by_cases h : p = c ∧ q = b
        · obtain ⟨rfl, rfl⟩ := h; exact hyc
        · simp only [bpE, h, if_false, mul_zero, add_zero] at hne
          exact hd1 p q hne
      · intro p q hneg
        by_cases h : p = c ∧ q = b
        · obtain ⟨rfl, rfl⟩ := h; exact hpos
        · simp only [bpE, h, if_false, mul_zero, add_zero] at hneg
          exact hd2 p q hneg
      · intro a
        rw [bpLd_add, bpLd_E, hd3, hb, hc]
        by_cases hab : a = b
        · subst hab; simp [hbc]
        · by_cases hac : a = c
          · subst hac; simp [hab]
          · simp [hab, hac]

end


section
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (part : V → Bool)

lemma bp_col_zero (hBip : ∀ i j, G.Adj i j → part i ≠ part j) (d : V → V → ℝ)
    (hd : ∀ a b, d a b ≠ 0 → G.Adj a b ∧ part a = true) (a : V) (ha : part a = true) :
    ∑ b, d b a = 0 := by
  refine Finset.sum_eq_zero (fun b _ => ?_)
  by_contra h
  have h1 := hd b a h
  have := hBip b a h1.1
  rw [h1.2, ha] at this; exact this rfl

lemma bp_row_zero (d : V → V → ℝ)
    (hd : ∀ a b, d a b ≠ 0 → G.Adj a b ∧ part a = true) (a : V) (ha : part a = false) :
    ∑ b, d a b = 0 := by
  refine Finset.sum_eq_zero (fun b _ => ?_)
  by_contra h
  have h1 := hd a b h
  rw [ha] at h1; exact Bool.false_ne_true h1.2

lemma bp_flow (hBip : ∀ i j, G.Adj i j → part i ≠ part j) (x : V → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hsum : xSum x (Finset.univ.filter (fun i => part i = true)) =
          xSum x (Finset.univ.filter (fun i => part i = false)))
    (hHall : ∀ S : Finset V, S ⊆ Finset.univ.filter (fun i => part i = true) →
          xSum x S ≤ xSum x (NeighborsF G S)) :
    ∃ y : V → V → ℝ, (∀ a b, 0 ≤ y a b) ∧ (∀ a b, y a b ≠ 0 → G.Adj a b ∧ part a = true) ∧
      ∀ a, bpLd y a = x a := by
  classical
  set K : Set (V → V → ℝ) := {y | (∀ a b, 0 ≤ y a b) ∧
    (∀ a b, y a b ≠ 0 → G.Adj a b ∧ part a = true) ∧ ∀ a, bpLd y a ≤ x a} with hKdef
  have hK : IsClosed K := by
    have e : K = (⋂ a, ⋂ b, {y : V → V → ℝ | 0 ≤ y a b}) ∩
        (⋂ a, ⋂ b, {y : V → V → ℝ | y a b ≠ 0 → G.Adj a b ∧ part a = true}) ∩
        ⋂ a, {y : V → V → ℝ | bpLd y a ≤ x a} := by
      ext y; simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]; tauto
    rw [e]
    refine ((isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_iInter fun a => isClosed_iInter fun b => ?_)).inter
      (isClosed_iInter fun a => isClosed_le (by unfold bpLd; fun_prop) continuous_const)
    by_cases h : G.Adj a b ∧ part a = true
    · have : {y : V → V → ℝ | y a b ≠ 0 → G.Adj a b ∧ part a = true} = Set.univ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun _ => h
      rw [this]; exact isClosed_univ
    · have : {y : V → V → ℝ | y a b ≠ 0 → G.Adj a b ∧ part a = true} = {y | y a b = 0} := by
        ext y; simp only [Set.mem_setOf_eq]
        constructor
        · intro hh; by_contra h'; exact h (hh h')
        · intro hh h'; exact absurd hh h'
      rw [this]; exact isClosed_eq (by fun_prop) continuous_const
  have hsub : K ⊆ Set.pi Set.univ (fun _ : V => Set.pi Set.univ (fun _ : V => Set.Icc (0:ℝ) 1)) := by
    intro y hy
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
    intro a b
    refine ⟨hy.1 a b, ?_⟩
    have h1 : y a b ≤ ∑ c, y a c :=
      Finset.single_le_sum (f := fun c => y a c) (fun c _ => hy.1 a c) (Finset.mem_univ b)
    have h2 : 0 ≤ ∑ c, y c a := Finset.sum_nonneg (fun c _ => hy.1 c a)
    have h3 := hy.2.2 a
    unfold bpLd at h3
    linarith [(hx a).2]
  have hcomp : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hK hsub
  have h0 : (fun _ _ => (0:ℝ)) ∈ K := by
    refine ⟨fun _ _ => le_rfl, fun a b h => absurd rfl h, fun a => ?_⟩
    simp [bpLd, (hx a).1]
  obtain ⟨y, hyK, hmax⟩ := hcomp.exists_isMaxOn ⟨_, h0⟩
    (by unfold bpTot; fun_prop : Continuous (bpTot (V := V))).continuousOn
  rw [isMaxOn_iff] at hmax
  obtain ⟨hy0, hy1, hy2⟩ := hyK
  have hT : ∀ a, part a = true → bpLd y a = x a := by
    by_contra hne
    push_neg at hne
    obtain ⟨i0, hi0, hne⟩ := hne
    have hlt0 : bpLd y i0 < x i0 := lt_of_le_of_ne (hy2 i0) hne
    have hA : ∀ j, Relation.ReflTransGen (bpStep G part y) i0 j → part j = false →
        bpLd y j = x j := by
      intro j hj hjf
      by_contra hne'
      have hlt : bpLd y j < x j := lt_of_le_of_ne (hy2 j) hne'
      obtain ⟨d, hd1, hd2, hd3⟩ := bp_augment G part hBip y hy1 i0 hi0 j hj
      have hij : i0 ≠ j := by rintro rfl; rw [hi0] at hjf; exact absurd hjf (by decide)
      set δ := min (x i0 - bpLd y i0) (x j - bpLd y j) with hδ
      have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
      have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε ≤ δ ∧
          ∀ p : V × V, d p.1 p.2 < 0 → ε * (-d p.1 p.2) ≤ y p.1 p.2 := by
        refine (eventually_mem_nhdsWithin).and (((eventually_le_nhds hδpos).filter_mono nhdsWithin_le_nhds).and
          (Filter.eventually_all.2 fun p => ?_))
        by_cases hp : d p.1 p.2 < 0
        · have hpos := hd2 _ _ hp
          have ht : Tendsto (fun ε : ℝ => ε * (-d p.1 p.2)) (𝓝 0) (𝓝 0) := by
            have h := (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (-d p.1 p.2)
            rw [zero_mul] at h
            exact h
          exact ((ht.eventually (eventually_le_nhds hpos)).filter_mono nhdsWithin_le_nhds).mono
            fun ε h _ => h
        · exact Filter.Eventually.of_forall fun ε h => absurd h hp
      obtain ⟨ε, hε0, hεδ, hεd⟩ := hev.exists
      set z : V → V → ℝ := fun p q => y p q + ε * d p q with hz
      have hzK : z ∈ K := by
        refine ⟨fun p q => ?_, fun p q hne => ?_, fun a => ?_⟩
        · by_cases hp : d p q < 0
          · have := hεd (p, q) hp; simp only [hz]; linarith
          · simp only [hz]; have := hy0 p q; nlinarith
        · by_cases h1 : y p q = 0
          · by_cases h2 : d p q = 0
            · exact absurd (by simp [hz, h1, h2]) hne
            · exact hd1 p q h2
          · exact hy1 p q h1
        · rw [hz, bpLd_add, hd3 a, hjf]
          by_cases ha : a = i0
          · subst ha
            simp only [if_true, hij, if_false, add_zero, mul_one]
            have := min_le_left (x a - bpLd y a) (x j - bpLd y j)
            linarith
          · by_cases hb : a = j
            · subst hb
              simp only [ha, if_false, if_true, zero_add]
              simp only [Bool.false_eq_true, if_false]
              have := min_le_right (x i0 - bpLd y i0) (x a - bpLd y a)
              linarith
            · simp only [ha, hb, if_false, add_zero, mul_zero]; exact hy2 a
      have htd : bpTot d = 1 := by
        rw [bpTot_eq_T G part hBip d hd1, Finset.sum_congr rfl (fun a _ => hd3 a)]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp [hi0, hjf]
      have := hmax z hzK
      rw [hz, bpTot_add, htd] at this
      linarith
    set R := Finset.univ.filter (fun v => Relation.ReflTransGen (bpStep G part y) i0 v) with hR
    set S := R.filter (fun v => part v = true) with hS
    have hSsub : S ⊆ Finset.univ.filter (fun i => part i = true) := by
      intro v hv; simp only [hS, Finset.mem_filter] at hv; simp [hv.2]
    have hi0S : i0 ∈ S := by simp [hS, hR, hi0, Relation.ReflTransGen.refl]
    have hN : ∀ j ∈ NeighborsF G S, Relation.ReflTransGen (bpStep G part y) i0 j ∧
        part j = false := by
      intro j hj
      simp only [NeighborsF, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and] at hj
      obtain ⟨⟨i, hiS, hadj⟩, _⟩ := hj
      simp only [hS, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
      refine ⟨hiS.1.tail (Or.inl ⟨hiS.2, hadj⟩), ?_⟩
      have := hBip i j hadj; rw [hiS.2] at this; simpa using this
    have hcol : ∀ j ∈ NeighborsF G S, bpLd y j = ∑ a ∈ S, y a j := by
      intro j hj
      obtain ⟨hjr, hjf⟩ := hN j hj
      unfold bpLd
      rw [bp_row_zero G part y hy1 j hjf, zero_add]
      refine (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => ?_)).symm
      by_contra hne
      have hpos : 0 < y a j := lt_of_le_of_ne (hy0 a j) (Ne.symm hne)
      have hra := hjr.tail (Or.inr ⟨hjf, hpos⟩)
      have hpa := (hy1 a j hne).2
      exact ha (by simp [hS, hR, hra, hpa])
    have key : xSum x (NeighborsF G S) < xSum x S := by
      calc xSum x (NeighborsF G S) = ∑ j ∈ NeighborsF G S, bpLd y j := by
            unfold xSum
            exact Finset.sum_congr rfl (fun j hj => (hA j (hN j hj).1 (hN j hj).2).symm)
        _ = ∑ j ∈ NeighborsF G S, ∑ a ∈ S, y a j := Finset.sum_congr rfl hcol
        _ = ∑ a ∈ S, ∑ j ∈ NeighborsF G S, y a j := Finset.sum_comm
        _ ≤ ∑ a ∈ S, ∑ j, y a j := Finset.sum_le_sum (fun a _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hy0 a j))
        _ = ∑ a ∈ S, bpLd y a := by
            refine Finset.sum_congr rfl (fun a ha => ?_)
            have hpa : part a = true := (Finset.mem_filter.1 ha).2
            simp [bpLd, bp_col_zero G part hBip y hy1 a hpa]
        _ < ∑ a ∈ S, x a := Finset.sum_lt_sum (fun a _ => hy2 a) ⟨i0, hi0S, hlt0⟩
        _ = xSum x S := rfl
    have := hHall S hSsub
    linarith
  have hF : ∀ a, part a = false → bpLd y a = x a := by
    have e1 : ∑ a ∈ Finset.univ.filter (fun i => part i = false), bpLd y a =
        ∑ a ∈ Finset.univ.filter (fun i => part i = false), x a := by
      rw [← bpTot_eq_F G part hBip y hy1, bpTot_eq_T G part hBip y hy1]
      rw [Finset.sum_congr rfl (fun a ha => hT a (Finset.mem_filter.1 ha).2)]
      exact hsum
    have := (Finset.sum_eq_sum_iff_of_le (fun a _ => hy2 a)).1 e1
    intro a ha
    exact this a (by simp [ha])
  refine ⟨y, hy0, hy1, fun a => ?_⟩
  cases ha : part a
  · exact hF a ha
  · exact hT a ha

end


section
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma bp_inc_xSum (W S : Finset V) :
    xSum (IncidenceVec W) S = ((S.filter (· ∈ W)).card : ℝ) := by
  simp [xSum, IncidenceVec, Finset.filter_mem_eq_inter]

lemma bp_xSum_comb (x y : V → ℝ) (a b : ℝ) (S : Finset V) :
    xSum (a • x + b • y) S = a * xSum x S + b * xSum y S := by
  simp [xSum, Finset.sum_add_distrib, Finset.mul_sum]

lemma bp_pm_card (G : SimpleGraph V) (W : Finset V) (M : V → V)
    (hM2 : ∀ v ∈ W, M (M v) = v) (hMW : ∀ v ∈ W, M v ∈ W) (A B : Finset V)
    (hAB : ∀ v ∈ W, v ∈ A → M v ∈ B) :
    (A.filter (· ∈ W)).card ≤ (B.filter (· ∈ W)).card := by
  refine Finset.card_le_card_of_injOn M ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hv ⊢
    exact ⟨hAB v hv.2 hv.1, hMW v hv.2⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    rw [← hM2 a ha.2, ← hM2 b hb.2, hab]

end

/-! ## Digraph part: double cover, flow, Birkhoff, loops -/

section
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma asg_xSum_sdiff (x : V → ℝ) (S T : Finset V) :
    xSum x (S \ T) - xSum x (T \ S) = xSum x S - xSum x T := by
  unfold xSum
  have h1 := Finset.sum_sdiff (f := x) (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  have h2 := Finset.sum_sdiff (f := x) (Finset.inter_subset_right (s₁ := S) (s₂ := T))
  rw [Finset.sdiff_inter_self_left] at h1
  rw [Finset.sdiff_inter_self_right] at h2
  linarith

def dcAdj (A : V → V → Prop) : V ⊕ V → V ⊕ V → Prop
  | Sum.inl a, Sum.inr b => A a b
  | Sum.inr b, Sum.inl a => A a b
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

def dcGraph (A : V → V → Prop) : SimpleGraph (V ⊕ V) where
  Adj := dcAdj A
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [dcAdj]⟩
  loopless := ⟨by
    intro u h
    cases u <;> simp [dcAdj] at h⟩

instance dcDec (A : V → V → Prop) [DecidableRel A] : DecidableRel (dcGraph A).Adj := by
  intro u v
  cases u <;> cases v <;> simp only [dcGraph, dcAdj] <;> infer_instance

lemma dc_adj_ll (A : V → V → Prop) (a c : V) : ¬ (dcGraph A).Adj (Sum.inl a) (Sum.inl c) := by
  simp [dcGraph, dcAdj]

lemma dc_adj_rr (A : V → V → Prop) (a c : V) : ¬ (dcGraph A).Adj (Sum.inr a) (Sum.inr c) := by
  simp [dcGraph, dcAdj]

lemma dc_adj_lr (A : V → V → Prop) (a b : V) : (dcGraph A).Adj (Sum.inl a) (Sum.inr b) ↔ A a b := by
  simp [dcGraph, dcAdj]

lemma dc_adj_rl (A : V → V → Prop) (a b : V) : (dcGraph A).Adj (Sum.inr b) (Sum.inl a) ↔ A a b := by
  simp [dcGraph, dcAdj]

lemma asg_flow (A : V → V → Prop) [DecidableRel A] (x : V → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hH : ∀ S : Finset V, xSum x S ≤ xSum x (GammaOut A S)) :
    ∃ y : V → V → ℝ, (∀ a b, 0 ≤ y a b) ∧ (∀ a b, y a b ≠ 0 → A a b) ∧
      (∀ a, ∑ b, y a b = x a) ∧ (∀ b, ∑ a, y a b = x b) := by
  classical
  let G := dcGraph A
  let part : V ⊕ V → Bool := Sum.isLeft
  have hBip : ∀ i j, G.Adj i j → part i ≠ part j := by
    intro i j h
    cases i <;> cases j <;> simp_all [G, dcGraph, dcAdj, part]
  let x' : V ⊕ V → ℝ := Sum.elim x x
  have hx' : ∀ i, 0 ≤ x' i ∧ x' i ≤ 1 := by
    intro i; cases i <;> simp [x', hx]
  have hsum : xSum x' (Finset.univ.filter (fun i => part i = true)) =
      xSum x' (Finset.univ.filter (fun i => part i = false)) := by
    unfold xSum
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [part, x']
  have hHall : ∀ S : Finset (V ⊕ V), S ⊆ Finset.univ.filter (fun i => part i = true) →
      xSum x' S ≤ xSum x' (NeighborsF G S) := by
    intro S hS
    have hSl : ∀ b, Sum.inr b ∉ S := by
      intro b hb
      have := hS hb
      simp [part] at this
    let S0 : Finset V := Finset.univ.filter (fun a => Sum.inl a ∈ S)
    have e1 : xSum x' S = xSum x S0 := by
      unfold xSum
      have : ∑ i ∈ S, x' i = ∑ i, if i ∈ S then x' i else 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [this, Fintype.sum_sum_type]
      simp [x', S0, hSl, Finset.sum_filter]
    have e2 : xSum x' (NeighborsF G S) = xSum x (GammaOut A S0) := by
      unfold xSum
      have : ∑ i ∈ NeighborsF G S, x' i = ∑ i, if i ∈ NeighborsF G S then x' i else 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [this, Fintype.sum_sum_type]
      have hl : ∀ a, Sum.inl a ∉ NeighborsF G S := by
        intro a ha
        simp only [NeighborsF, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨⟨i, hi, hadj⟩, _⟩ := ha
        cases i with
        | inl c => exact dc_adj_ll A c a hadj
        | inr c => exact hSl c hi
      have hr : ∀ b, Sum.inr b ∈ NeighborsF G S ↔ b ∈ GammaOut A S0 := by
        intro b
        simp only [NeighborsF, GammaOut, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and, S0]
        constructor
        · rintro ⟨⟨i, hi, hadj⟩, _⟩
          cases i with
          | inl c => exact ⟨c, hi, (dc_adj_lr A c b).1 hadj⟩
          | inr c => exact absurd hi (hSl c)
        · rintro ⟨c, hc, hA⟩
          exact ⟨⟨Sum.inl c, hc, (dc_adj_lr A c b).2 hA⟩, hSl b⟩
      simp [x', hl, hr, Finset.sum_filter]
    rw [e1, e2]
    exact hH S0
  obtain ⟨y', hy0, hy1, hy2⟩ := bp_flow G part hBip x' hx' hsum hHall
  have hyll : ∀ a c, y' (Sum.inl a) (Sum.inl c) = 0 := by
    intro a c; by_contra h; exact dc_adj_ll A a c (hy1 _ _ h).1
  have hyr : ∀ b u, y' (Sum.inr b) u = 0 := by
    intro b u; by_contra h; have := (hy1 _ _ h).2; simp [part] at this
  refine ⟨fun a b => y' (Sum.inl a) (Sum.inr b), fun a b => hy0 _ _, fun a b h => ?_,
    fun a => ?_, fun b => ?_⟩
  · exact (dc_adj_lr A a b).1 (hy1 _ _ h).1
  · have := hy2 (Sum.inl a)
    simp only [bpLd, Fintype.sum_sum_type, hyll, hyr, Finset.sum_const_zero, zero_add,
      add_zero, x', Sum.elim_inl] at this
    exact this
  · have := hy2 (Sum.inr b)
    simp only [bpLd, Fintype.sum_sum_type, hyr, hyll, Finset.sum_const_zero, zero_add,
      add_zero, x', Sum.elim_inr] at this
    exact this


lemma asg_of_perm (A : V → V → Prop) (W : Finset V) (σ : Equiv.Perm V)
    (hW : ∀ v, σ v ∈ W ↔ v ∈ W) (hA : ∀ v ∈ W, A v (σ v)) : IsAssignable A W := by
  refine ⟨σ.subtypePerm hW, fun v => ?_⟩
  rw [Equiv.Perm.subtypePerm_apply]
  exact hA v.1 v.2

lemma asg_insert (A : V → V → Prop) (W : Finset V) (hW : IsAssignable A W) (a : V)
    (ha : a ∉ W) (haa : A a a) : IsAssignable A (insert a W) := by
  obtain ⟨σ, hσ⟩ := hW
  let τ : Equiv.Perm V := Equiv.Perm.ofSubtype σ
  have hτmem : ∀ v (hv : v ∈ W), τ v = (σ ⟨v, hv⟩).1 := by
    intro v hv
    simp [τ, Equiv.Perm.ofSubtype_apply_of_mem σ hv]
  have hτnot : ∀ v, v ∉ W → τ v = v := by
    intro v hv
    exact Equiv.Perm.ofSubtype_apply_of_not_mem σ hv
  refine asg_of_perm A (insert a W) τ ?_ ?_
  · intro v
    by_cases hv : v ∈ W
    · rw [hτmem v hv]
      simp [hv, (σ ⟨v, hv⟩).2]
    · rw [hτnot v hv]
  · intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · rw [hτnot v ha]; exact haa
    · rw [hτmem v hv]; exact hσ ⟨v, hv⟩

lemma asg_gen_mem (A : V → V → Prop) (W : Finset V) (hW : IsAssignable A W) :
    IncidenceVec W ∈ AssignableSubgraphPolytope A :=
  subset_convexHull ℝ _ ⟨W, hW, rfl⟩

lemma asg_convex (A : V → V → Prop) : Convex ℝ (AssignableSubgraphPolytope A) :=
  convex_convexHull ℝ _

lemma asg_hull_le_one (A : V → V → Prop) (z : V → ℝ) (hz : z ∈ AssignableSubgraphPolytope A)
    (a : V) : z a ≤ 1 := by
  unfold AssignableSubgraphPolytope at hz
  have : convexHull ℝ {x : V → ℝ | ∃ W : Finset V, IsAssignable A W ∧ x = IncidenceVec W} ⊆
      {z : V → ℝ | z a ≤ 1} := by
    apply convexHull_min
    · rintro x ⟨W, _, rfl⟩
      simp only [Set.mem_setOf_eq, IncidenceVec]; split_ifs <;> norm_num
    · intro x hx y hy p q hp hq hpq
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith
  exact this hz

lemma asg_loop_aug (A : V → V → Prop) (a : V) (haa : A a a) (z : V → ℝ)
    (hz : z ∈ AssignableSubgraphPolytope A) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 - z a) :
    (fun i => z i + if i = a then t else 0) ∈ AssignableSubgraphPolytope A := by
  let C : Set (V → ℝ) := {z | z ∈ AssignableSubgraphPolytope A ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 - z a →
    (fun i => z i + if i = a then t else 0) ∈ AssignableSubgraphPolytope A}
  have hC : AssignableSubgraphPolytope A ⊆ C := by
    unfold AssignableSubgraphPolytope
    apply convexHull_min
    · rintro x ⟨W, hW, rfl⟩
      refine ⟨asg_gen_mem A W hW, fun t ht0 ht1 => ?_⟩
      by_cases ha : a ∈ W
      · have ht : t = 0 := by
          simp only [IncidenceVec, ha, if_true] at ht1; linarith
        have : (fun i => IncidenceVec W i + if i = a then t else 0) = IncidenceVec W := by
          funext i; simp [ht]
        rw [this]
        exact asg_gen_mem A W hW
      · have hsplit : (fun i => IncidenceVec W i + if i = a then t else 0) =
            (1 - t) • IncidenceVec W + t • IncidenceVec (insert a W) := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, IncidenceVec, Finset.mem_insert]
          by_cases hi : i = a
          · subst hi; simp [ha]
          · by_cases hiW : i ∈ W <;> simp [hi, hiW]
        rw [hsplit]
        have ht1' : t ≤ 1 := by
          simp only [IncidenceVec, ha, if_false] at ht1; linarith
        exact asg_convex A (asg_gen_mem A W hW)
          (asg_gen_mem A _ (asg_insert A W hW a ha haa)) (by linarith) ht0 (by ring)
    · intro z1 hz1 z2 hz2 p q hp hq hpq
      obtain ⟨hz1m, hz1t⟩ := hz1
      obtain ⟨hz2m, hz2t⟩ := hz2
      refine ⟨asg_convex A hz1m hz2m hp hq hpq, fun t ht0 ht1 => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1 ⊢
      have h1 := asg_hull_le_one A z1 hz1m a
      have h2 := asg_hull_le_one A z2 hz2m a
      set s := 1 - (p * z1 a + q * z2 a) with hs
      have hs' : s = p * (1 - z1 a) + q * (1 - z2 a) := by rw [hs]; linarith
      by_cases hs0 : s = 0
      · have ht : t = 0 := by linarith
        have : (fun i => p * z1 i + q * z2 i + if i = a then t else 0) = p • z1 + q • z2 := by
          funext i; simp [ht]
        rw [this]
        exact asg_convex A hz1m hz2m hp hq hpq
      · have hspos : 0 < s := lt_of_le_of_ne (by nlinarith) (Ne.symm hs0)
        set t1 := t * (1 - z1 a) / s with ht1d
        set t2 := t * (1 - z2 a) / s with ht2d
        have ht1_0 : 0 ≤ t1 := by rw [ht1d]; apply div_nonneg; nlinarith; linarith
        have ht2_0 : 0 ≤ t2 := by rw [ht2d]; apply div_nonneg; nlinarith; linarith
        have hts : t / s ≤ 1 := by rw [div_le_one hspos]; linarith
        have ht1_1 : t1 ≤ 1 - z1 a := by
          rw [ht1d, mul_div_right_comm]
          calc t / s * (1 - z1 a) ≤ 1 * (1 - z1 a) :=
                mul_le_mul_of_nonneg_right hts (by linarith)
            _ = 1 - z1 a := one_mul _
        have ht2_1 : t2 ≤ 1 - z2 a := by
          rw [ht2d, mul_div_right_comm]
          calc t / s * (1 - z2 a) ≤ 1 * (1 - z2 a) :=
                mul_le_mul_of_nonneg_right hts (by linarith)
            _ = 1 - z2 a := one_mul _
        have hcomb : (fun i => p * z1 i + q * z2 i + if i = a then t else 0) =
            p • (fun i => z1 i + if i = a then t1 else 0) +
              q • (fun i => z2 i + if i = a then t2 else 0) := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          by_cases hi : i = a
          · simp only [hi, if_true, ht1d, ht2d]
            field_simp
            rw [hs']; ring
          · simp [hi]
        rw [hcomb]
        exact asg_convex A (hz1t t1 ht1_0 ht1_1) (hz2t t2 ht2_0 ht2_1) hp hq hpq
  exact (hC hz).2 t ht0 ht1

theorem asg_core (A : V → V → Prop) [DecidableRel A] :
    AssignableSubgraphPolytope A =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ S : Finset V, xSum x (S \ GammaOut A S) - xSum x (GammaOut A S \ S) ≤ 0} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨W, ⟨σ, hσ⟩, rfl⟩
      refine ⟨fun i => ?_, fun S => ?_⟩
      · simp only [IncidenceVec]; split_ifs <;> norm_num
      · rw [asg_xSum_sdiff, bp_inc_xSum, bp_inc_xSum, sub_nonpos]
        norm_cast
        refine Finset.card_le_card_of_injOn (fun v => if h : v ∈ W then (σ ⟨v, h⟩).1 else v)
          ?_ ?_
        · intro v hv
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hv ⊢
          rw [dif_pos hv.2]
          refine ⟨?_, (σ ⟨v, hv.2⟩).2⟩
          simp only [GammaOut, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, hv.1, hσ ⟨v, hv.2⟩⟩
        · intro v hv w hw hvw
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          simp only [dif_pos hv.2, dif_pos hw.2] at hvw
          have := σ.injective (Subtype.ext hvw)
          simpa using this
    · intro x hx y hy a b ha hb hab
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨fun i => ?_, fun S => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx1 i; have := hy1 i
        constructor <;> nlinarith
      · rw [bp_xSum_comb, bp_xSum_comb]
        have := hx2 S; have := hy2 S
        nlinarith
  · rintro x ⟨hx, hS⟩
    have hH : ∀ S : Finset V, xSum x S ≤ xSum x (GammaOut A S) := by
      intro S; have := hS S; rw [asg_xSum_sdiff] at this; linarith
    obtain ⟨y, hy0, hy1, hrow, hcol⟩ := asg_flow A x hx hH
    set Mx : Matrix V V ℝ := fun a b => (if a = b then 1 - x a else 0) + y a b with hMx
    have hMds : Mx ∈ doublyStochastic ℝ V := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
      · simp only [hMx]
        have := hy0 i j; have := hx i
        split_ifs <;> linarith
      · have := hrow i
        simp only [hMx, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        linarith
      · have := hcol j
        simp only [hMx, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linarith
    obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hMds
    have hentry : ∀ a b, Mx a b = ∑ σ, w σ * (if σ a = b then 1 else 0) := by
      intro a b
      rw [← hwM]
      simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have hpm : ∀ σ : Equiv.Perm V, w σ ≠ 0 →
        IsAssignable A (Finset.univ.filter (fun a => σ a ≠ a)) := by
      intro σ hσ
      have hpos : 0 < w σ := lt_of_le_of_ne (hw0 σ) (Ne.symm hσ)
      have hadj : ∀ a, σ a ≠ a → A a (σ a) := by
        intro a ha
        have h1 : w σ ≤ Mx a (σ a) := by
          rw [hentry]
          have := Finset.single_le_sum (f := fun τ : Equiv.Perm V => w τ * (if τ a = σ a then 1 else 0))
            (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (Finset.mem_univ σ)
          simpa using this
        simp only [hMx, if_neg (Ne.symm ha), zero_add] at h1
        exact hy1 _ _ (by linarith)
      refine asg_of_perm A _ σ ?_ ?_
      · intro v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact σ.injective.ne_iff
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hadj v hv
    set z : V → ℝ := fun a => x a - y a a with hz
    have hzsum : z = ∑ σ, w σ • IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a)) := by
      funext a
      have h1 := hentry a a
      simp only [hMx, if_true] at h1
      have h2 : ∑ σ : Equiv.Perm V, w σ * (if σ a = a then 1 else 0) +
          ∑ σ : Equiv.Perm V, w σ * (if σ a ≠ a then 1 else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← hw1]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        split_ifs <;> simp_all
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, IncidenceVec, Finset.mem_filter, Finset.mem_univ,
        true_and, hz]
      linarith
    have hzmem : z ∈ AssignableSubgraphPolytope A := by
      rw [hzsum]
      have hz' : ∑ σ, w σ • IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a)) =
          ∑ σ, w σ • (if w σ = 0 then IncidenceVec (∅ : Finset V)
            else IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a))) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        by_cases h : w σ = 0 <;> simp [h]
      rw [hz']
      unfold AssignableSubgraphPolytope
      refine (convex_convexHull ℝ _).sum_mem (fun σ _ => hw0 σ) hw1 (fun σ _ => ?_)
      apply subset_convexHull
      by_cases h : w σ = 0
      · simp only [h, if_true]
        refine ⟨∅, ⟨Equiv.refl _, fun v => (Finset.notMem_empty v.1 v.2).elim⟩, rfl⟩
      · simp only [h, if_false]
        exact ⟨_, hpm σ h, rfl⟩
    -- add the loops one by one
    have hloops : ∀ L : Finset V,
        (fun i => z i + if i ∈ L then y i i else 0) ∈ AssignableSubgraphPolytope A := by
      intro L
      induction L using Finset.induction_on with
      | empty => simpa using hzmem
      | @insert a L haL ih =>
        by_cases hya : y a a = 0
        · have : (fun i => z i + if i ∈ insert a L then y i i else 0) =
              (fun i => z i + if i ∈ L then y i i else 0) := by
            funext i
            by_cases hi : i = a
            · subst hi; simp [haL, hya]
            · simp [hi]
          rw [this]; exact ih
        · have haa : A a a := hy1 a a hya
          have hya0 : 0 ≤ y a a := hy0 a a
          have := asg_loop_aug A a haa _ ih (y a a) hya0 (by
            simp only [haL, if_false, add_zero, hz]
            have := (hx a).2
            linarith)
          have e : (fun i => z i + if i ∈ insert a L then y i i else 0) =
              (fun i => (z i + if i ∈ L then y i i else 0) + if i = a then y a a else 0) := by
            funext i
            by_cases hi : i = a
            · subst hi; simp [haL]
            · simp [hi]
          rw [e]; exact this
    have := hloops Finset.univ
    have e : (fun i => z i + if i ∈ (Finset.univ : Finset V) then y i i else 0) = x := by
      funext i; simp [hz]
    rw [e] at this
    exact this

end

end Disjunctive.ExtendedFormulations

open Disjunctive.ExtendedFormulations


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    [DecidableRel A] :
    AssignableSubgraphPolytope A =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ S : Finset V, xSum x (S \ GammaOut A S) - xSum x (GammaOut A S \ S) ≤ 0} := by
  exact asg_core A
