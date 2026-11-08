-- Prove2me | solution 1 for FanInSemigroup.wordLanguage_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:41:23.822114+00:00
-- url     : https://prove2.me/submissions/c7d1203d-2cc5-4389-bcee-96e5f429918b

import Definitions.Def_FanInSemigroup_wordLanguage

set_option autoImplicit false

open FanInSemigroup in
theorem solution {S : Type*} [Semigroup S] [Finite S] (a : S) :
    (wordLanguage a).IsRegular := by
  let M : DFA S (Option S) :=
    ⟨fun o x => some (Option.elim o x (fun s => s * x)), none, {some a}⟩
  have hfold : ∀ (l : List S) (s : S), M.evalFrom (some s) l = some (wordProd s l) := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons x l ih =>
      intro s
      rw [DFA.evalFrom_cons]
      exact ih (s * x)
  rw [Language.isRegular_iff]
  refine ⟨Option S, Fintype.ofFinite _, M, ?_⟩
  ext w
  rw [DFA.mem_accepts]
  cases w with
  | nil =>
    constructor
    · intro h
      have h' : (none : Option S) = some a := h
      cases h'
    · rintro ⟨a₀, l, h, _⟩
      cases h
  | cons a₀ l =>
    change M.evalFrom (some a₀) l ∈ ({some a} : Set (Option S)) ↔ _
    rw [hfold, Set.mem_singleton_iff, Option.some_inj]
    constructor
    · intro h
      exact ⟨a₀, l, rfl, h⟩
    · rintro ⟨b, l', h, h'⟩
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
      exact h'
