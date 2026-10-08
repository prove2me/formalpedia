-- Prove2me | solution 1 for Disjunctive.ExtendedFormulations.pms_polytope_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:44:41.131989+00:00
-- url     : https://prove2.me/submissions/1a3773f8-76c4-4d37-b999-0047a9c3423d

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

theorem pms_bip_core (G : SimpleGraph V)
    [DecidableRel G.Adj] (part : V → Bool) (hBip : ∀ i j, G.Adj i j → part i ≠ part j) :
    PMSPolytope G =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        xSum x (Finset.univ.filter (fun i => part i = true)) =
          xSum x (Finset.univ.filter (fun i => part i = false)) ∧
        ∀ S : Finset V, S ⊆ Finset.univ.filter (fun i => part i = true) →
          xSum x S ≤ xSum x (NeighborsF G S)} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨W, ⟨M, hM1, hM2⟩, rfl⟩
      have hMW : ∀ v ∈ W, M v ∈ W := fun v hv => (hM1 v hv).1
      have hflip : ∀ v ∈ W, part (M v) = !part v := by
        intro v hv
        have := hBip v (M v) (hM1 v hv).2
        cases h1 : part v <;> cases h2 : part (M v) <;> simp_all
      refine ⟨fun i => ?_, ?_, ?_⟩
      · simp only [IncidenceVec]; split_ifs <;> norm_num
      · rw [bp_inc_xSum, bp_inc_xSum]
        norm_cast
        apply le_antisymm
        · apply bp_pm_card G W M hM2 hMW
          intro v hv hA
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
          rw [hflip v hv, hA]; rfl
        · apply bp_pm_card G W M hM2 hMW
          intro v hv hA
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
          rw [hflip v hv, hA]; rfl
      · intro S hS
        rw [bp_inc_xSum, bp_inc_xSum]
        norm_cast
        apply bp_pm_card G W M hM2 hMW
        intro v hv hvS
        have hpv : part v = true := by
          have := hS hvS; simpa using this
        simp only [NeighborsF, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨v, hvS, (hM1 v hv).2⟩, fun hMS => ?_⟩
        have h1 : part (M v) = true := by have := hS hMS; simpa using this
        rw [hflip v hv, hpv] at h1
        exact absurd h1 (by decide)
    · intro x hx y hy a b ha hb hab
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨hy1, hy2, hy3⟩ := hy
      refine ⟨fun i => ?_, ?_, fun S hS => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx1 i; have := hy1 i
        constructor <;> nlinarith
      · rw [bp_xSum_comb, bp_xSum_comb, hx2, hy2]
      · rw [bp_xSum_comb, bp_xSum_comb]
        have := hx3 S hS; have := hy3 S hS
        nlinarith
  · rintro x ⟨hx, hsum, hHall⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := bp_flow G part hBip x hx hsum hHall
    have hyd : ∀ a, y a a = 0 := by
      intro a; by_contra h; exact (hy1 a a h).1.ne rfl
    set Mx : Matrix V V ℝ := fun a b => (if a = b then 1 - x a else 0) + y a b + y b a with hMx
    have hMds : Mx ∈ doublyStochastic ℝ V := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
      · simp only [hMx]
        have := hy0 i j; have := hy0 j i; have := hx i
        split_ifs <;> linarith
      · have := hy2 i
        simp only [bpLd] at this
        simp only [hMx, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        linarith
      · have := hy2 j
        simp only [bpLd] at this
        simp only [hMx, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linarith
    obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hMds
    have hentry : ∀ a b, Mx a b = ∑ σ, w σ * (if σ a = b then 1 else 0) := by
      intro a b
      rw [← hwM]
      simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have hpm : ∀ σ : Equiv.Perm V, w σ ≠ 0 →
        HasPerfectMatching G (Finset.univ.filter (fun a => σ a ≠ a)) := by
      intro σ hσ
      have hpos : 0 < w σ := lt_of_le_of_ne (hw0 σ) (Ne.symm hσ)
      have hadj : ∀ a, σ a ≠ a → G.Adj a (σ a) := by
        intro a ha
        have h1 : w σ ≤ Mx a (σ a) := by
          rw [hentry]
          have := Finset.single_le_sum (f := fun τ : Equiv.Perm V => w τ * (if τ a = σ a then 1 else 0))
            (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (Finset.mem_univ σ)
          simpa using this
        simp only [hMx, if_neg (Ne.symm ha), zero_add] at h1
        by_cases h2 : y a (σ a) = 0
        · have h3 : y (σ a) a ≠ 0 := by intro h3; rw [h2, h3] at h1; linarith
          exact (hy1 _ _ h3).1.symm
        · exact (hy1 _ _ h2).1
      refine ⟨fun a => if part a = true then σ a else σ⁻¹ a, ?_, ?_⟩
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        by_cases hp : part v = true
        · simp only [hp, if_true]
          exact ⟨fun h => hv (σ.injective h), hadj v hv⟩
        · have hp' : part v = false := by simpa using hp
          simp only [hp', Bool.false_eq_true, if_false]
          have hb : σ⁻¹ v ≠ v := by
            intro h; apply hv; conv_lhs => rw [← h]; simp
          have hσb : σ (σ⁻¹ v) = v := by simp
          refine ⟨by rw [hσb]; exact Ne.symm hb, ?_⟩
          have := hadj (σ⁻¹ v) (by rw [hσb]; exact Ne.symm hb)
          rw [hσb] at this
          exact this.symm
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        by_cases hp : part v = true
        · have hq : part (σ v) = false := by
            have := hBip v (σ v) (hadj v hv); rw [hp] at this; simpa using this
          simp [hp, hq]
        · have hb : σ⁻¹ v ≠ v := by
            intro h; apply hv; conv_lhs => rw [← h]; simp
          have hσb : σ (σ⁻¹ v) = v := by simp
          have hadjb := hadj (σ⁻¹ v) (by rw [hσb]; exact Ne.symm hb)
          rw [hσb] at hadjb
          have hq : part (σ⁻¹ v) = true := by
            have := hBip _ _ hadjb
            cases h1 : part v <;> cases h2 : part (σ⁻¹ v) <;> simp_all
          have hp' : part v = false := by simpa using hp
          simp only [hp', Bool.false_eq_true, if_false, hq, if_true, hσb]
    have hxsum : x = ∑ σ, w σ • IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a)) := by
      funext a
      have h1 := hentry a a
      simp only [hMx, if_true, hyd, add_zero] at h1
      have h2 : ∑ σ : Equiv.Perm V, w σ * (if σ a = a then 1 else 0) +
          ∑ σ : Equiv.Perm V, w σ * (if σ a ≠ a then 1 else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← hw1]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        split_ifs <;> simp_all
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, IncidenceVec, Finset.mem_filter, Finset.mem_univ,
        true_and]
      linarith
    rw [hxsum]
    have hz : ∑ σ, w σ • IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a)) =
        ∑ σ, w σ • (if w σ = 0 then IncidenceVec (∅ : Finset V)
          else IncidenceVec (Finset.univ.filter (fun a => σ a ≠ a))) := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      by_cases h : w σ = 0 <;> simp [h]
    rw [hz]
    unfold PMSPolytope
    refine (convex_convexHull ℝ _).sum_mem (fun σ _ => hw0 σ) hw1 (fun σ _ => ?_)
    apply subset_convexHull
    by_cases h : w σ = 0
    · simp only [h, if_true]
      exact ⟨∅, ⟨id, by simp, by simp⟩, rfl⟩
    · simp only [h, if_false]
      exact ⟨_, hpm σ h, rfl⟩

end

end Disjunctive.ExtendedFormulations

open Disjunctive.ExtendedFormulations


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (part : V → Bool) (hBip : ∀ i j, G.Adj i j → part i ≠ part j) :
    PMSPolytope G =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        xSum x (Finset.univ.filter (fun i => part i = true)) =
          xSum x (Finset.univ.filter (fun i => part i = false)) ∧
        ∀ S : Finset V, S ⊆ Finset.univ.filter (fun i => part i = true) →
          xSum x S ≤ xSum x (NeighborsF G S)} := by
  exact pms_bip_core G part hBip
