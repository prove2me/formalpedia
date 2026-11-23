-- Prove2me | solution 1 for DistributedMWC440.UpperBound.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:40:40.008699+00:00
-- url     : https://prove2.me/submissions/6395085f-f93d-41fb-9c64-7fc93fa02a6f

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound
namespace Lemma53

variable {V : Type}

private lemma walkWeight_nonneg (W : WGraph V) {u v : V}
    (P : W.graph.Walk u v) : 0 ≤ walkWeight W P := by
  induction P with
  | nil => simp [OAI.PlanarL1.walkLength]
  | @cons u w _ h P ih =>
      exact add_nonneg (W.nonnegative _ _ h) ih

private lemma dist_le_walk (W : WGraph V) {u v : V}
    (P : W.graph.Walk u v) : dist W u v ≤ walkWeight W P := by
  unfold dist OuterplanarL1Tan.Linear.WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact walkWeight_nonneg W Q
  · exact ⟨P, rfl⟩

private lemma dist_self (W : WGraph V) (u : V) : dist W u u = 0 := by
  apply le_antisymm
  · simpa [OAI.PlanarL1.walkLength] using
      (dist_le_walk W (SimpleGraph.Walk.nil : W.graph.Walk u u))
  · unfold dist OuterplanarL1Tan.Linear.WeightedGraph.distance OAI.PlanarL1.graphDistance
    apply le_csInf
    · exact ⟨0, ⟨SimpleGraph.Walk.nil, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact walkWeight_nonneg W P

private lemma walkLength_append {G : SimpleGraph V} (l : V → V → ℝ)
    {u v w : V} (P : G.Walk u v) (Q : G.Walk v w) :
    OAI.PlanarL1.walkLength l (P.append Q) =
      OAI.PlanarL1.walkLength l P + OAI.PlanarL1.walkLength l Q := by
  induction P with
  | nil => simp [OAI.PlanarL1.walkLength]
  | @cons u x _ hux P ih =>
      simp [OAI.PlanarL1.walkLength, ih, add_assoc]

private lemma walkLength_concat {G : SimpleGraph V} (l : V → V → ℝ)
    {u v w : V} (P : G.Walk u v) (h : G.Adj v w) :
    OAI.PlanarL1.walkLength l (P.concat h) =
      OAI.PlanarL1.walkLength l P + l v w := by
  simp [SimpleGraph.Walk.concat, walkLength_append, OAI.PlanarL1.walkLength]

private lemma ldd_upper [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (S : Finset V) (k d ε : ℝ) (hε : 0 < ε) (δ : Shifts S)
    (T : LDDTree W S k d ε δ) (s : S) (v : V) :
    T.label (some v) ≤ (1 + ε) *
      (2 * deltaMax S k d - trunc S k d δ s + dist W s.val v) := by
  let f : W.graph →g augmentedGraph W S :=
    { toFun := some
      map_rel' := by
        intro u w huw
        refine ⟨?_, Or.inl huw⟩
        intro h
        exact huw.ne (Option.some.inj h) }
  have hsAdj : (augmentedGraph W S).Adj none (some s.val) := by
    simp [augmentedGraph, s.property]
  have hmap {a b : V} (P : W.graph.Walk a b) :
      OAI.PlanarL1.walkLength (augmentedLength W S k d δ) (P.map f) =
        walkWeight W P := by
    induction P with
    | nil => rfl
    | @cons a b c hab P ih =>
        change augmentedLength W S k d δ (some a) (some b) +
          OAI.PlanarL1.walkLength (augmentedLength W S k d δ) (P.map f) =
          W.length a b + walkWeight W P
        rw [ih]
        simp [augmentedLength]
  have hlen (P : W.graph.Walk s.val v) :
      OAI.PlanarL1.walkLength (augmentedLength W S k d δ)
          (SimpleGraph.Walk.cons hsAdj (P.map f)) =
        (2 * deltaMax S k d - trunc S k d δ s) + walkWeight W P := by
    change augmentedLength W S k d δ none (some s.val) +
      OAI.PlanarL1.walkLength (augmentedLength W S k d δ) (P.map f) = _
    rw [hmap]
    simp [augmentedLength, s.property]
  have hP : ∀ P : W.graph.Walk s.val v,
      T.label (some v) ≤ (1 + ε) * ((2 * deltaMax S k d - trunc S k d δ s) +
        walkWeight W P) := by
    intro P
    simpa [hlen] using T.approximate v (SimpleGraph.Walk.cons hsAdj (P.map f))
  have hA : 0 < 1 + ε := by linarith
  have hdiv : ∀ P : W.graph.Walk s.val v,
      T.label (some v) / (1 + ε) -
        (2 * deltaMax S k d - trunc S k d δ s) ≤ walkWeight W P := by
    intro P
    have hmul : T.label (some v) ≤
        ((2 * deltaMax S k d - trunc S k d δ s) + walkWeight W P) * (1 + ε) := by
      simpa [mul_comm] using hP P
    have h := (div_le_iff₀ hA).2 hmul
    linarith
  have hle : T.label (some v) / (1 + ε) -
      (2 * deltaMax S k d - trunc S k d δ s) ≤ dist W s.val v := by
    unfold dist OuterplanarL1Tan.Linear.WeightedGraph.distance OAI.PlanarL1.graphDistance
    obtain ⟨P₀⟩ := hW.preconnected s.val v
    apply le_csInf
    · exact ⟨_, ⟨P₀, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact hdiv P
  have h : T.label (some v) / (1 + ε) ≤
      2 * deltaMax S k d - trunc S k d δ s + dist W s.val v := by linarith
  simpa [mul_comm] using (div_le_iff₀ hA).1 h

private lemma exists_seed_path [Fintype V] [DecidableEq V]
    (W : WGraph V) (S : Finset V) (k d ε : ℝ) (δ : Shifts S)
    (T : LDDTree W S k d ε δ) (v : V) :
    ∃ r : V, r ∈ S ∧ T.parent (some r) = none ∧ T.center v = some r ∧
      ∃ P : W.graph.Walk r v,
        augmentedLength W S k d δ none (some r) + walkWeight W P ≤
          T.label (some v) := by
  generalize hn : T.depth (some v) = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
      cases hp : T.parent (some v) with
      | none =>
          have hd : T.depth (some v) = 1 := by
            have hstep := T.depth_step v
            rw [hp, T.root_depth] at hstep
            omega
          refine ⟨v, ?_, hp, ?_, SimpleGraph.Walk.nil, ?_⟩
          · have he := T.edge v
            rw [hp] at he
            rcases he with ⟨hne, h | h⟩
            · simpa [augmentedGraph] using h
            · exact h
          · simp [LDDTree.center, hd]
          · have hdsc := T.descent v
            rw [hp, T.root_label] at hdsc
            simpa [OAI.PlanarL1.walkLength] using hdsc
      | some u =>
          have hstep := T.depth_step v
          rw [hp] at hstep
          have hlt : T.depth (some u) < n := by omega
          rcases ih (T.depth (some u)) hlt u rfl with
            ⟨r, hrS, hrparent, hrcenter, P, hP⟩
          have hcenter : T.center v = T.center u := by
            have hupos : 0 < T.depth (some u) := by
              have hu := T.depth_step u
              omega
            unfold LDDTree.center
            rw [← hstep]
            simp only [Nat.add_sub_cancel]
            conv_lhs =>
              rw [show T.depth (some u) = (T.depth (some u) - 1) + 1 by omega]
            rw [Function.iterate_succ_apply, hp]
          have hAdj : W.graph.Adj u v := by
            have he := T.edge v
            rw [hp] at he
            rcases he with ⟨hne, h | h⟩
            · exact h
            · exact h.symm
          have hdsc := T.descent v
          rw [hp] at hdsc
          change T.label (some u) + W.length u v ≤ T.label (some v) at hdsc
          refine ⟨r, hrS, hrparent, hcenter.trans hrcenter, P.concat hAdj, ?_⟩
          change augmentedLength W S k d δ none (some r) +
            OAI.PlanarL1.walkLength W.length (P.concat hAdj) ≤ T.label (some v)
          rw [walkLength_concat]
          change augmentedLength W S k d δ none (some r) +
            (walkWeight W P + W.length u v) ≤ T.label (some v)
          linarith

end Lemma53
end DistributedMWC440.UpperBound

open DistributedMWC440.UpperBound
open DistributedMWC440.UpperBound.Lemma53

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S : Finset V) (hS : 2 ≤ S.card) (k d ε : ℝ)
    (hk : 1/2 ≤ k) (hd : 0 < d) (hε : 0 < ε)
    (δ : Shifts S) (hδ : ValidShifts S k d δ) (s : S) (v : V)
    (hsafe : Safe W S k d ε δ s v) (harrival : dist W s.val v - trunc S k d δ s ≤ 0)
    (T : LDDTree W S k d ε δ) : T.center v = some s.val := by
  rcases exists_seed_path W S k d ε δ T v with
    ⟨r, hrS, hrparent, hcenter, P, hP⟩
  rw [hcenter]
  apply congrArg some
  by_contra hrs
  let r' : S := ⟨r, hrS⟩
  have hrs' : r' ≠ s := by
    intro heq
    apply hrs
    exact congrArg Subtype.val heq
  have hcomp := hsafe r' hrs'
  change dist W s.val v - trunc S k d δ s <
    dist W r v - trunc S k d δ r' - 2 * ε * deltaMax S k d at hcomp
  have hdist : dist W r v ≤ walkWeight W P := dist_le_walk W P
  have hupper : T.label (some v) ≤ (1 + ε) *
      (2 * deltaMax S k d - trunc S k d δ s + dist W s.val v) :=
    ldd_upper W hW S k d ε hε δ T s v
  have hP' : (2 * deltaMax S k d - trunc S k d δ r') + walkWeight W P ≤
      T.label (some v) := by
    simpa [r', augmentedLength, hrS] using hP
  have hprod : ε * (dist W s.val v - trunc S k d δ s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hε.le harrival
  nlinarith
