-- Prove2me | solution 1 for DynOracleConn.probe_simulation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:48.528614+00:00
-- url     : https://prove2.me/submissions/a2d857e9-34d9-4f04-b87c-f92ea9f7268b

import Definitions.Def_DynOracleConn_Gadget

open DynOracleConn

namespace AuxProbeSim

lemma epochGraph_adj_iff {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d)
    (i : Option (Fin d)) (a b : Fin n) :
    (epochGraph e X i).Adj a b ↔
      a ≠ b ∧
        ((∃ p ∈ fixedEdges d, s(e p.1, e p.2) = s(a, b)) ∨
         (∃ p ∈ variableEdges X, s(e p.1, e p.2) = s(a, b)) ∨
         (∃ i₀, i = some i₀ ∧ s(e GV.t, e (GV.v false i₀)) = s(a, b))) := by
  cases i with
  | none =>
      simp only [epochGraph, gadget, SimpleGraph.fromEdgeSet_adj, gadgetEdges, List.mem_append,
        exists_prop, reduceCtorEq, false_and, exists_false, or_false]
      constructor
      · rintro ⟨⟨p, hp | hp, heq⟩, hne⟩
        · exact ⟨hne, Or.inl ⟨p, hp, heq.symm⟩⟩
        · exact ⟨hne, Or.inr ⟨p, hp, heq.symm⟩⟩
      · rintro ⟨hne, ⟨p, hp, heq⟩ | ⟨p, hp, heq⟩⟩
        · exact ⟨⟨p, Or.inl hp, heq.symm⟩, hne⟩
        · exact ⟨⟨p, Or.inr hp, heq.symm⟩, hne⟩
  | some i₀ =>
      simp only [epochGraph, withT, SimpleGraph.sup_adj, gadget, SimpleGraph.fromEdgeSet_adj,
        Set.mem_singleton_iff, gadgetEdges, List.mem_append, Option.some.injEq, exists_eq_left']
      constructor
      · rintro (⟨⟨p, hp | hp, heq⟩, hne⟩ | ⟨heq, hne⟩)
        · exact ⟨hne, Or.inl ⟨p, hp, heq.symm⟩⟩
        · exact ⟨hne, Or.inr (Or.inl ⟨p, hp, heq.symm⟩)⟩
        · exact ⟨hne, Or.inr (Or.inr heq.symm)⟩
      · rintro ⟨hne, ⟨p, hp, heq⟩ | ⟨p, hp, heq⟩ | heq⟩
        · exact Or.inl ⟨⟨p, Or.inl hp, heq.symm⟩, hne⟩
        · exact Or.inl ⟨⟨p, Or.inr hp, heq.symm⟩, hne⟩
        · exact Or.inr ⟨heq.symm, hne⟩

lemma sym2_map_inj {n d : ℕ} (e : GV d ↪ Fin n) {x₁ y₁ x₂ y₂ : GV d} :
    (s(e x₁, e y₁) : Sym2 (Fin n)) = s(e x₂, e y₂) ↔ (s(x₁, y₁) : Sym2 (GV d)) = s(x₂, y₂) := by
  simp only [Sym2.eq_iff, Function.Embedding.apply_eq_iff_eq]

lemma mem_variableEdges_sym2 {d : ℕ} (X : PPHPInst d) (x y : GV d) :
    (∃ p ∈ variableEdges X, (s(p.1, p.2) : Sym2 (GV d)) = s(x, y)) ↔
      (∃ (b₁ b₂ : Bool) (j i' : Fin d),
        (s(GV.l b₁ j, GV.u b₂ i') : Sym2 (GV d)) = s(x, y) ∧
          pOracle X (i', j) = some (xor b₁ b₂)) ∨
      (∃ (b₁ : Bool) (i' j : Fin d),
        (s(GV.v b₁ i', GV.r b₁ j) : Sym2 (GV d)) = s(x, y) ∧
          (pOracle X (i', j)).isSome = true) := by
  unfold variableEdges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨p, ⟨i', rfl | rfl | rfl | rfl⟩, heq⟩
    · left
      refine ⟨false, xor false (X.2 (X.1 i')), X.1 i', i', heq, ?_⟩
      simp [pOracle]
    · left
      refine ⟨true, xor true (X.2 (X.1 i')), X.1 i', i', heq, ?_⟩
      simp [pOracle]
    · right
      refine ⟨false, i', X.1 i', heq, ?_⟩
      simp [pOracle]
    · right
      refine ⟨true, i', X.1 i', heq, ?_⟩
      simp [pOracle]
  · rintro (⟨b₁, b₂, j, i', heq, hpo⟩ | ⟨b₁, i', j, heq, hpo⟩)
    · simp only [pOracle] at hpo
      split_ifs at hpo with hij
      · simp only [Option.some.injEq] at hpo
        subst hij
        have hb2 : b₂ = xor b₁ (X.2 (X.1 i')) := by
          rw [hpo]; cases b₁ <;> cases b₂ <;> rfl
        subst hb2
        cases b₁
        · exact ⟨_, ⟨i', Or.inl rfl⟩, heq⟩
        · exact ⟨_, ⟨i', Or.inr (Or.inl rfl)⟩, heq⟩
    · simp only [pOracle] at hpo
      split_ifs at hpo with hij
      · subst hij
        cases b₁
        · exact ⟨_, ⟨i', Or.inr (Or.inr (Or.inl rfl))⟩, heq⟩
        · exact ⟨_, ⟨i', Or.inr (Or.inr (Or.inr rfl))⟩, heq⟩
      · simp at hpo

def varProbe {d : ℕ} (x y : GV d) : Option (Fin d × Fin d) × (Option (Option Bool) → Bool) :=
  match x, y with
  | .l b₁ j, .u b₂ i' => (some (i', j), fun r => r == some (some (xor b₁ b₂)))
  | .u b₂ i', .l b₁ j => (some (i', j), fun r => r == some (some (xor b₁ b₂)))
  | .v b₁ i', .r b₂ j =>
      if b₁ = b₂ then
        (some (i', j), fun r => match r with | some (some _) => true | _ => false)
      else (none, fun _ => false)
  | .r b₂ j, .v b₁ i' =>
      if b₁ = b₂ then
        (some (i', j), fun r => match r with | some (some _) => true | _ => false)
      else (none, fun _ => false)
  | _, _ => (none, fun _ => false)

lemma varProbe_spec {d : ℕ} (x y : GV d) (X : PPHPInst d) :
    (∃ p ∈ variableEdges X, (s(p.1, p.2) : Sym2 (GV d)) = s(x, y)) ↔
      (varProbe x y).2 ((varProbe x y).1.map (pOracle X)) = true := by
  rw [mem_variableEdges_sym2]
  rcases x with _ | _ | ⟨bx, jx⟩ | ⟨bx, jx⟩ | ⟨bx, ix⟩ | ⟨bx, ix⟩ <;>
    rcases y with _ | _ | ⟨by_, jy⟩ | ⟨by_, jy⟩ | ⟨by_, iy⟩ | ⟨by_, iy⟩
  all_goals
    dsimp [varProbe]
    try (simp [Sym2.eq_iff]; done)
  · -- l bx jx, u by_ iy
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq]
    constructor
    · rintro (⟨b₁, b₂, j, i', heq, hpo⟩ | ⟨b₁, i', j, heq, _⟩)
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · injection h1 with hb1 hj; injection h2 with hb2 hi
          subst hb1 hj hb2 hi; exact hpo
        · nomatch h1
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
    · intro hpo
      exact Or.inl ⟨bx, by_, jx, iy, rfl, hpo⟩
  · -- r bx jx, v by_ iy
    split_ifs with hbb
    · subst hbb
      simp only [Option.map_some]
      constructor
      · rintro (⟨b₁, b₂, j, i', heq, _⟩ | ⟨b₁, i', j, heq, hpo⟩)
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
          · nomatch h1
          · injection h1 with _ hi; injection h2 with _ hj
            subst hi hj
            cases hp : pOracle X (i', j) with
            | none => rw [hp] at hpo; simp at hpo
            | some _ => rfl
      · intro hr
        refine Or.inr ⟨by_, iy, jx, Sym2.eq_swap, ?_⟩
        cases hp : pOracle X (iy, jx) with
        | none => rw [hp] at hr; nomatch hr
        | some _ => rfl
    · constructor
      · rintro (⟨b₁, b₂, j, i', heq, _⟩ | ⟨b₁, i', j, heq, _⟩)
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
          · nomatch h1
          · injection h1 with hb1 _; injection h2 with hb2 _
            subst hb1; exact False.elim (hbb hb2)
      · intro h; nomatch h
  · -- u bx ix, l by_ jy
    simp only [Option.map_some, beq_iff_eq]
    constructor
    · rintro (⟨b₁, b₂, j, i', heq, hpo⟩ | ⟨b₁, i', j, heq, _⟩)
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
        · nomatch h1
        · injection h1 with hb1 hj; injection h2 with hb2 hi
          subst hb1 hj hb2 hi; exact hpo
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
    · intro hpo
      exact Or.inl ⟨by_, bx, jy, ix, Sym2.eq_swap, hpo⟩
  · -- v bx ix, r by_ jy
    split_ifs with hbb
    · subst hbb
      simp only [Option.map_some]
      constructor
      · rintro (⟨b₁, b₂, j, i', heq, _⟩ | ⟨b₁, i', j, heq, hpo⟩)
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
          · injection h1 with _ hi; injection h2 with _ hj
            subst hi hj
            cases hp : pOracle X (i', j) with
            | none => rw [hp] at hpo; simp at hpo
            | some _ => rfl
          · nomatch h1
      · intro hr
        refine Or.inr ⟨bx, ix, jy, rfl, ?_⟩
        cases hp : pOracle X (ix, jy) with
        | none => rw [hp] at hr; nomatch hr
        | some _ => rfl
    · constructor
      · rintro (⟨b₁, b₂, j, i', heq, _⟩ | ⟨b₁, i', j, heq, _⟩)
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nomatch h1
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
          · injection h1 with hb1 _; injection h2 with hb2 _
            subst hb1; exact False.elim (hbb hb2)
          · nomatch h1
      · intro h; nomatch h

end AuxProbeSim

theorem solution {n d : ℕ} (e : GV d ↪ Fin n) (i : Option (Fin d)) (a b : Fin n) :
    ∃ (o : Option (Fin d × Fin d)) (f : Option (Option Bool) → Bool),
      ∀ X : PPHPInst d, ((epochGraph e X i).Adj a b ↔ f (o.map (pOracle X)) = true) := by
  classical
  by_cases hab : a = b
  · refine ⟨none, fun _ => false, fun X => ?_⟩
    subst hab
    simp
  · by_cases ha : ∃ x : GV d, e x = a
    · obtain ⟨x, rfl⟩ := ha
      by_cases hb : ∃ y : GV d, e y = b
      · obtain ⟨y, rfl⟩ := hb
        have hxy : x ≠ y := fun h => hab (congrArg e h)
        by_cases hfix : (∃ p ∈ fixedEdges d, (s(p.1, p.2) : Sym2 (GV d)) = s(x, y)) ∨
            (∃ i₀, i = some i₀ ∧ (s(GV.t, GV.v false i₀) : Sym2 (GV d)) = s(x, y))
        · refine ⟨none, fun _ => true, fun X => ?_⟩
          rw [AuxProbeSim.epochGraph_adj_iff]
          simp only [AuxProbeSim.sym2_map_inj, Option.map_none, iff_true]
          refine ⟨hab, ?_⟩
          rcases hfix with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inr h2)
        · refine ⟨(AuxProbeSim.varProbe x y).1, (AuxProbeSim.varProbe x y).2, fun X => ?_⟩
          rw [AuxProbeSim.epochGraph_adj_iff]
          simp only [AuxProbeSim.sym2_map_inj]
          rw [← AuxProbeSim.varProbe_spec x y X]
          push Not at hfix
          rcases hfix with ⟨hnoFix, hnoT⟩
          constructor
          · rintro ⟨_, h1 | h2 | h3⟩
            · exact False.elim (by obtain ⟨p, hp, heq⟩ := h1; exact hnoFix p hp heq)
            · exact h2
            · exact False.elim (by obtain ⟨i₀, hi₀, heq⟩ := h3; exact hnoT i₀ hi₀ heq)
          · intro h2
            exact ⟨hab, Or.inr (Or.inl h2)⟩
      · refine ⟨none, fun _ => false, fun X => ?_⟩
        rw [AuxProbeSim.epochGraph_adj_iff]
        simp only [Option.map_none, Bool.false_eq_true, iff_false, not_and]
        intro _ h
        rcases h with ⟨p, _, heq⟩ | ⟨p, _, heq⟩ | ⟨i₀, _, heq⟩ <;>
          (rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2⟩ | ⟨h2, _⟩ <;> exact hb ⟨_, h2⟩)
    · refine ⟨none, fun _ => false, fun X => ?_⟩
      rw [AuxProbeSim.epochGraph_adj_iff]
      simp only [Option.map_none, Bool.false_eq_true, iff_false, not_and]
      intro _ h
      rcases h with ⟨p, _, heq⟩ | ⟨p, _, heq⟩ | ⟨i₀, _, heq⟩ <;>
        (rw [Sym2.eq_iff] at heq; rcases heq with ⟨h1, _⟩ | ⟨_, h1⟩ <;> exact ha ⟨_, h1⟩)
