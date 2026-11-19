-- Prove2me | solution 1 for CircTrichotomy.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:13:49.213857+00:00
-- url     : https://prove2.me/submissions/4be94e1f-ccd3-46cf-af5f-b51224e171bc

import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_Reduces

set_option autoImplicit false

namespace CircTrichotomy.LemmaA3Aux
open CircTrichotomy

/-- A finite family of sign conditions over a base inside `Σ⁺` is a Boolean combination. -/
lemma boolComb_signs {α : Type} (G : Set (Language α)) (U : Language α)
    (hU : BoolComb G U) (hUpos : ∀ z ∈ U, z ≠ []) (c : Language α → Prop)
    (s : Finset (Language α)) (hs : ∀ Q ∈ s, BoolComb G Q) :
    BoolComb G {z | z ∈ U ∧ ∀ Q ∈ s, (z ∈ Q ↔ c Q)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : {z | z ∈ U ∧ ∀ Q ∈ (∅ : Finset (Language α)), (z ∈ Q ↔ c Q)} = U := by
      ext z; exact ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩
    rw [e]; exact hU
  | insert Q s hQ ih =>
    have ih' := ih (fun Q' hQ' => hs Q' (Finset.mem_insert_of_mem hQ'))
    have hQc := hs Q (Finset.mem_insert_self _ _)
    by_cases hc : c Q
    · have e : {z | z ∈ U ∧ ∀ Q' ∈ insert Q s, (z ∈ Q' ↔ c Q')} =
          {z | z ∈ {z | z ∈ U ∧ ∀ Q' ∈ s, (z ∈ Q' ↔ c Q')} ∧ z ∈ Q} := by
        ext z
        simp only [Finset.mem_insert, Set.mem_ofPred_eq, forall_eq_or_imp]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2.2 hc⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, ⟨fun _ => hc, fun _ => h2⟩, h3⟩
      rw [e]; exact BoolComb.inter ih' hQc
    · have e : {z | z ∈ U ∧ ∀ Q' ∈ insert Q s, (z ∈ Q' ↔ c Q')} =
          {z | z ∈ {z | z ∈ U ∧ ∀ Q' ∈ s, (z ∈ Q' ↔ c Q')} ∧ z ∈ posCompl Q} := by
        ext z
        simp only [Finset.mem_insert, Set.mem_ofPred_eq, forall_eq_or_imp, posCompl]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h3⟩, hUpos z h1, fun h => hc (h2.1 h)⟩
        · rintro ⟨⟨h1, h3⟩, -, h2⟩
          exact ⟨h1, ⟨fun h => absurd h h2, fun h => absurd h hc⟩, h3⟩
      rw [e]; exact BoolComb.inter ih' (BoolComb.compl hQc)

end CircTrichotomy.LemmaA3Aux

open CircTrichotomy CircTrichotomy.LemmaA3Aux in
theorem solution {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) (x : SyntSemigroup L) : Reduces (syntPreimage L x) L := by
  classical
  obtain ⟨σ, hσ, M, hM⟩ := hreg
  induction x using Con.induction_on with
  | H w =>
  set wl := wordToList w with hwl
  have hwl0 : wl ≠ [] := by simp [hwl, wordToList]
  refine ⟨fun b => [b], 1, Nat.one_pos, fun _ => rfl, ?_⟩
  have hfm : ∀ z : List α, z.flatMap (fun b => [b]) = z := by
    intro z; induction z with
    | nil => rfl
    | cons a t ih => simp [ih]
  -- the two-sided quotients
  let Q : List α → List α → Language α := fun u v => {z | z ≠ [] ∧ u ++ z ++ v ∈ L}
  let G : Set (Language α) :=
    {N | ∃ u v : List α, N = {z | z ≠ [] ∧ u ++ z.flatMap (fun b => [b]) ++ v ∈ L}}
  have hQG : ∀ u v, Q u v ∈ G := by
    intro u v; refine ⟨u, v, ?_⟩; ext z; simp [Q, hfm]
  -- finitely many quotients
  let g : σ × Set σ → Language α := fun pT => {z | z ≠ [] ∧ M.evalFrom pT.1 z ∈ pT.2}
  have hQg : ∀ u v, Q u v = g (M.evalFrom M.start u, {s | M.evalFrom s v ∈ M.accept}) := by
    intro u v; ext z
    simp only [Q, g, Set.mem_ofPred_eq, ← hM, DFA.mem_accepts, DFA.eval,
      DFA.evalFrom_of_append]
  let QS : Set (Language α) := Set.range (fun uv : List α × List α => Q uv.1 uv.2)
  have hQS : QS.Finite := (Set.finite_range g).subset (by
    rintro _ ⟨⟨u, v⟩, rfl⟩; exact ⟨_, (hQg u v).symm⟩)
  let U : Language α := {z | z ∈ Q [] [] ∨ z ∈ posCompl (Q [] [])}
  have hU : BoolComb G U :=
    BoolComb.union (BoolComb.base (hQG [] [])) (BoolComb.compl (BoolComb.base (hQG [] [])))
  have hUpos : ∀ z ∈ U, z ≠ [] := by
    rintro z (h | h)
    · exact h.1
    · exact h.1
  have hmain := boolComb_signs G U hU hUpos (fun N => wl ∈ N) hQS.toFinset (by
    intro N hN
    rw [Set.Finite.mem_toFinset] at hN
    obtain ⟨⟨u, v⟩, rfl⟩ := hN
    exact BoolComb.base (hQG u v))
  have e : syntPreimage L (w : SyntSemigroup L) =
      {z | z ∈ U ∧ ∀ N ∈ hQS.toFinset, (z ∈ N ↔ wl ∈ N)} := ?_
  · rw [e]; exact hmain
  ext z
  simp only [syntPreimage, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨z', rfl, hz'⟩
    have hz0 : wordToList z' ≠ [] := by simp [wordToList]
    have hcon : syntCon L z' w := (Con.eq _).1 hz'
    refine ⟨?_, ?_⟩
    · by_cases h : wordToList z' ∈ Q [] []
      · exact Or.inl h
      · exact Or.inr ⟨hz0, h⟩
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      simp only [Q, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨hwl0, (hcon u v).1 h.2⟩, fun h => ⟨hz0, (hcon u v).2 h.2⟩⟩
  · rintro ⟨hzU, hz⟩
    have hz0 := hUpos z hzU
    obtain ⟨a, t, rfl⟩ : ∃ a t, z = a :: t := by
      cases z with
      | nil => exact absurd rfl hz0
      | cons a t => exact ⟨a, t, rfl⟩
    refine ⟨⟨a, t⟩, rfl, (Con.eq _).2 ?_⟩
    intro u v
    have := hz _ ⟨(u, v), rfl⟩
    simp only [Q, Set.mem_ofPred_eq] at this
    constructor
    · intro h; exact (this.1 ⟨hz0, h⟩).2
    · intro h; exact (this.2 ⟨hwl0, h⟩).2
