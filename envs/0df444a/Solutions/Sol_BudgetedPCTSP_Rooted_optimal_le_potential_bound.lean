-- Prove2me | solution 1 for BudgetedPCTSP.Rooted.optimal_le_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T21:18:04.906611+00:00
-- url     : https://prove2.me/submissions/c43fcb8c-79d8-42da-9cb4-7d54117013e7

import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_potential
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep
import Theorems.Thm_BudgetedPCTSP_Rooted_dual_feasible
import Theorems.Thm_BudgetedPCTSP_Rooted_lemma1

/-! ===== PC_Run ===== -/

/-! # Piece A: PD(λ) has a complete run. -/

namespace PCRun
open BudgetedPCTSP.Rooted

/-- Termination measure: `2·|comps| + |active|`. -/
def measure {V : Type} (s : PDState V) : ℕ := 2 * s.comps.card + s.active.card

theorem measure_lt {V : Type} [Fintype V] [DecidableEq V] {I : Instance V} {lam : ℝ}
    {s t : PDState V} (h : PDStep I lam s t) : measure t < measure s := by
  cases h with
  | neutral Δ S hΔ hS ht =>
    have := Finset.card_erase_add_one hS
    simp only [measure]
    omega
  | edge Δ S₁ S₂ u v hΔ he ht =>
    obtain ⟨_, h1, h2, _, _, hne, hact⟩ := he
    have h2' : S₂ ∈ s.comps.erase S₁ := Finset.mem_erase.mpr ⟨fun h => hne h.symm, h2⟩
    have c1 := Finset.card_erase_add_one h1
    have c2 := Finset.card_erase_add_one h2'
    have c3 := Finset.card_insert_le (S₁ ∪ S₂) ((s.comps.erase S₁).erase S₂)
    have a3 := Finset.card_insert_le (S₁ ∪ S₂) ((s.active.erase S₁).erase S₂)
    have a4 : ((s.active.erase S₁).erase S₂).card < s.active.card := by
      rcases hact with ha | ha
      · exact lt_of_le_of_lt (Finset.card_erase_le) (Finset.card_erase_lt_of_mem ha)
      · by_cases h12 : S₂ = S₁
        · exact absurd h12.symm hne
        · have : S₂ ∈ s.active.erase S₁ := Finset.mem_erase.mpr ⟨h12, ha⟩
          exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem this) Finset.card_erase_le
    simp only [measure]
    omega

open Classical in
theorem exists_step {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (s : PDState V) (h : s.active.Nonempty) : ∃ t, PDStep I lam s t := by
  let E : Finset (Finset V × Finset V × V × V) :=
    (s.comps ×ˢ s.comps ×ˢ Finset.univ ×ˢ Finset.univ).filter
      (fun p => IsEdgeCandidate I s p.1 p.2.1 p.2.2.1 p.2.2.2)
  let A : Finset ℝ := s.active.image (neutralTime s)
  let B : Finset ℝ := E.image (fun p => edgeTime I lam s p.1 p.2.1 p.2.2.1 p.2.2.2)
  have hne : (A ∪ B).Nonempty := (h.image _).mono Finset.subset_union_left
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = (A ∪ B).min' hne := ⟨_, rfl⟩
  have hΔ : IsNextEventTime I lam s Δ := by
    rw [hΔdef]
    constructor
    · intro S hS
      exact Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS))
    · intro S₁ S₂ u v he
      apply Finset.min'_le
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(S₁, S₂, u, v), ?_, rfl⟩
      simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨⟨he.2.1, he.2.2.1⟩, he⟩
  have hm := Finset.min'_mem (A ∪ B) hne
  rw [← hΔdef] at hm
  rcases Finset.mem_union.mp hm with hA | hB
  · obtain ⟨S, hS, ht⟩ := Finset.mem_image.mp hA
    exact ⟨_, PDStep.neutral s Δ S hΔ hS ht⟩
  · obtain ⟨⟨S₁, S₂, u, v⟩, hp, ht⟩ := Finset.mem_image.mp hB
    have he : IsEdgeCandidate I s S₁ S₂ u v := (Finset.mem_filter.mp hp).2
    exact ⟨_, PDStep.edge s Δ S₁ S₂ u v hΔ he ht⟩

theorem aux {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ) :
    ∀ k, ∀ s : PDState V, measure s ≤ k → IsReachable I lam s →
      ∃ s' : PDState V, IsCompleteRun I lam s' := by
  intro k
  induction k with
  | zero =>
    intro s hs hr
    by_cases h : s.active = ∅
    · exact ⟨s, hr, h⟩
    · obtain ⟨t, ht⟩ := exists_step I lam s (Finset.nonempty_iff_ne_empty.mpr h)
      have := measure_lt ht
      omega
  | succ k ih =>
    intro s hs hr
    by_cases h : s.active = ∅
    · exact ⟨s, hr, h⟩
    · obtain ⟨t, ht⟩ := exists_step I lam s (Finset.nonempty_iff_ne_empty.mpr h)
      have := measure_lt ht
      exact ih t (by omega) (hr.tail ht)

theorem exists_complete_run {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (hlam : 0 ≤ lam) : ∃ s : PDState V, IsCompleteRun I lam s :=
  aux I lam _ PDState.init le_rfl Relation.ReflTransGen.refl

end PCRun

/-! ===== PC_Support ===== -/

/-! # Piece B: duals are supported on ever-active sets. -/

namespace PCSupport
open BudgetedPCTSP.Rooted

theorem raise_ne_zero {V : Type} [Fintype V] [DecidableEq V] (s : PDState V) (Δ : ℝ)
    (S : Finset V) (h : raise s Δ S ≠ 0) : s.y S ≠ 0 ∨ S ∈ s.active := by
  by_contra hc
  push Not at hc
  apply h
  simp [raise, hc.1, hc.2]

theorem support_everActive {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (s : PDState V) (hs : IsReachable I lam s) :
    s.active ⊆ s.everActive ∧ ∀ S : Finset V, s.y S ≠ 0 → S ∈ s.everActive := by
  induction hs with
  | refl =>
    refine ⟨fun x hx => hx, fun S hS => ?_⟩
    exact absurd rfl hS
  | tail _ hstep ih =>
    obtain ⟨hA, hY⟩ := ih
    cases hstep with
    | neutral Δ S hΔ hS ht =>
      refine ⟨fun x hx => hA (Finset.mem_of_mem_erase hx), fun T hT => ?_⟩
      rcases raise_ne_zero _ Δ T hT with h | h
      · exact hY T h
      · exact hA h
    | edge Δ S₁ S₂ u v hΔ he ht =>
      refine ⟨fun x hx => ?_, fun T hT => ?_⟩
      · simp only [Finset.mem_insert] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (hA (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)))
      · apply Finset.mem_insert_of_mem
        rcases raise_ne_zero _ Δ T hT with h | h
        · exact hY T h
        · exact hA h

end PCSupport

/-! ===== PC_Walk ===== -/

/-! # Piece C: a closed walk meeting both `T` and its complement crosses `δ(T)` at least twice. -/

namespace PCWalk
open BudgetedPCTSP.Rooted

open Classical in
theorem crossSum_nonneg {V : Type} (T : Finset V) (l : List (Sym2 V)) :
    0 ≤ (l.map (fun e => if Crosses T e then (1 : ℝ) else 0)).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  split_ifs <;> norm_num

open Classical in
theorem one_le_crossSum {V : Type} {G : SimpleGraph V} (T : Finset V) :
    ∀ {a b : V} (q : G.Walk a b), (a ∈ T ↔ b ∉ T) →
      (1 : ℝ) ≤ (q.edges.map (fun e => if Crosses T e then (1 : ℝ) else 0)).sum := by
  intro a b q
  induction q with
  | @nil u => intro h; by_cases ha : u ∈ T <;> simp_all
  | @cons u v w h q ih =>
    intro hab
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
    have h0 := crossSum_nonneg T q.edges
    by_cases hc : Crosses T s(u, v)
    · rw [if_pos hc]; linarith
    · rw [if_neg hc, zero_add]
      apply ih
      have huv : u ∈ T ↔ v ∈ T := by
        by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> simp only [hu, hv]
        · exact absurd ⟨u, hu, v, hv, rfl⟩ hc
        · exact absurd ⟨v, hv, u, hu, Sym2.eq_swap⟩ hc
      rw [← huv]; exact hab

open Classical in
theorem two_le_crossings {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {r : V}
    (p : G.Walk r r) (T : Finset V) (hin : ∃ x ∈ p.support, x ∈ T)
    (hout : ∃ x ∈ p.support, x ∉ T) :
    (2 : ℝ) ≤ (p.edges.map (fun e => if Crosses T e then (1 : ℝ) else 0)).sum := by
  have key : ∀ x (hx : x ∈ p.support), (r ∈ T ↔ x ∉ T) →
      (2 : ℝ) ≤ (p.edges.map (fun e => if Crosses T e then (1 : ℝ) else 0)).sum := by
    intro x hx hrx
    have he : (p.takeUntil x hx).edges ++ (p.dropUntil x hx).edges = p.edges := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
    rw [← he, List.map_append, List.sum_append]
    have h1 := one_le_crossSum T (p.takeUntil x hx) hrx
    have h2 := one_le_crossSum T (p.dropUntil x hx) (by tauto)
    linarith
  by_cases hr : r ∈ T
  · obtain ⟨x, hx, hxT⟩ := hout
    exact key x hx (by tauto)
  · obtain ⟨x, hx, hxT⟩ := hin
    exact key x hx (by tauto)

end PCWalk

/-! ===== PC_Fit ===== -/

/-! # Piece D: dual fitting — part (ii) of the goal. -/

namespace PCFit
open BudgetedPCTSP.Rooted
open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Number of edges of a list that cross `S`, as a real. -/
noncomputable def cross (S : Finset V) (l : List (Sym2 V)) : ℝ :=
  (l.map (fun e => if Crosses S e then (1 : ℝ) else 0)).sum

theorem cross_nonneg (S : Finset V) (l : List (Sym2 V)) : 0 ≤ cross S l := by
  unfold cross
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  split_ifs <;> norm_num

theorem edgeLoad_eq (y : Finset V → ℝ) (e : Sym2 V) :
    edgeLoad y e = ∑ S, if Crosses S e then y S else 0 := by
  unfold edgeLoad
  rw [Finset.sum_filter]

theorem sum_edgeLoad (y : Finset V → ℝ) :
    ∀ l : List (Sym2 V), (l.map (edgeLoad y)).sum = ∑ S, y S * cross S l
  | [] => by simp [cross]
  | e :: l => by
    rw [List.map_cons, List.sum_cons, sum_edgeLoad y l, edgeLoad_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [cross, List.map_cons, List.sum_cons]
    split_ifs <;> ring

theorem load_le_budget (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) (s : PDState V)
    (hs : IsReachable I lam s) (p : I.G.Walk I.r I.r) (hp : I.IsFeasibleTour p) :
    (p.edges.map (edgeLoad s.y)).sum ≤ lam * I.D := by
  have hfeas := (dual_feasible I lam hlam s hs).1
  calc (p.edges.map (edgeLoad s.y)).sum
      ≤ (p.edges.map (fun e => lam * I.c e)).sum :=
        List.sum_le_sum (fun e he => hfeas e (p.edges_subset_edgeSet he))
    _ = lam * I.walkCost p := by
        unfold Instance.walkCost
        rw [List.sum_map_mul_left]
    _ ≤ lam * I.D := mul_le_mul_of_nonneg_left hp hlam

theorem part2 (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) (s : PDState V)
    (hs : IsCompleteRun I lam s) (p : I.G.Walk I.r I.r) (hp : I.IsFeasibleTour p)
    (O : Finset V) (hO : O ∈ sPlus s) (hsub : p.support.toFinset ⊆ O)
    (hmin : ∀ O' ∈ sPlus s, p.support.toFinset ⊆ O' → ¬ O' ⊂ O) :
    (p.support.toFinset.card : ℝ) ≤ lam * I.D + potential s.y O := by
  set P := p.support.toFinset with hPdef
  have hy0 := (dual_feasible I lam hlam s hs.1).2
  have hsupp := (PCSupport.support_everActive I lam s hs.1).2
  -- sets meeting `P`
  set A := O.ssubsets.filter (fun S => ¬ Disjoint S P) with hA
  set B := O.ssubsets.filter (fun S => Disjoint S P) with hB
  have hsplit : ∑ T ∈ O.ssubsets, s.y T = ∑ T ∈ A, s.y T + ∑ T ∈ B, s.y T := by
    rw [hA, hB, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- (b): sets meeting P are crossed twice
  have hAle : 2 * ∑ T ∈ A, s.y T ≤ lam * I.D := by
    calc 2 * ∑ T ∈ A, s.y T = ∑ T ∈ A, 2 * s.y T := by rw [Finset.mul_sum]
      _ ≤ ∑ T ∈ A, s.y T * cross T p.edges := by
          refine Finset.sum_le_sum fun T hT => ?_
          by_cases hyT : s.y T = 0
          · rw [hyT]; simp
          rw [hA, Finset.mem_filter, Finset.mem_ssubsets] at hT
          obtain ⟨hTO, hTP⟩ := hT
          have hTact : T ∈ sPlus s := Finset.mem_insert_of_mem (hsupp T hyT)
          have hPT : ¬ P ⊆ T := fun h => hmin T hTact h hTO
          obtain ⟨x, hxP, hxT⟩ := Finset.not_subset.1 hPT
          obtain ⟨z, hzT, hzP⟩ := Finset.not_disjoint_iff.1 hTP
          have h2 : (2 : ℝ) ≤ cross T p.edges :=
            PCWalk.two_le_crossings p T ⟨z, List.mem_toFinset.1 hzP, hzT⟩
              ⟨x, List.mem_toFinset.1 hxP, hxT⟩
          have := hy0 T
          nlinarith
      _ ≤ ∑ T, s.y T * cross T p.edges :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun T _ _ => mul_nonneg (hy0 T) (cross_nonneg T _))
      _ = (p.edges.map (edgeLoad s.y)).sum := (sum_edgeLoad s.y p.edges).symm
      _ ≤ lam * I.D := load_le_budget I lam hlam s hs.1 p hp
  -- (a): sets disjoint from P live inside O \ P
  have hBle : 2 * ∑ T ∈ B, s.y T ≤ ((O \ P).card : ℝ) := by
    have hBsub : B ⊆ (O \ P).powerset := by
      intro T hT
      rw [hB, Finset.mem_filter, Finset.mem_ssubsets] at hT
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff]
      exact ⟨hT.1.subset hx, Finset.disjoint_left.1 hT.2 hx⟩
    have := Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun T _ _ => hy0 T)
    have h1 := lemma1 I lam hlam s hs (O \ P)
    linarith
  have hcard : ((O \ P).card : ℝ) + P.card = O.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  unfold potential
  rw [hsplit]
  linarith

end PCFit

open BudgetedPCTSP.Rooted in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (I : Instance V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ s : PDState V, IsCompleteRun I lam s) ∧
    ∀ s : PDState V, IsCompleteRun I lam s →
      ∀ p : I.G.Walk I.r I.r, I.IsFeasibleTour p →
        ∀ O ∈ sPlus s, p.support.toFinset ⊆ O →
          (∀ O' ∈ sPlus s, p.support.toFinset ⊆ O' → ¬ O' ⊂ O) →
            (p.support.toFinset.card : ℝ) ≤ lam * I.D + potential s.y O :=
  ⟨PCRun.exists_complete_run I lam hlam,
   fun s hs p hp O hO hsub hmin => PCFit.part2 I lam hlam s hs p hp O hO hsub hmin⟩
