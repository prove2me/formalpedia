-- Prove2me | solution 1 for GaugeFunctor.orbitF_forgets_only_stuff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T21:02:15.289037+00:00
-- url     : https://prove2.me/submissions/64ae1b1a-3fb9-4d07-ac63-97383b2943ec

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem ofs_main (X : Graph) (G : Type) [Group G] :
    (orbitF X G).Full ∧ (orbitF X G).EssSurj ∧
      ((orbitF X G).Faithful ↔ (IsEmpty (Fin X.nV) ∨ Subsingleton G)) := by
  refine ⟨⟨fun {A B} f => ?_⟩, ⟨fun q => ?_⟩, ⟨fun hF => ?_, fun h => ⟨fun {A B} f f' _ => ?_⟩⟩⟩
  · have h1 : (Quotient.mk (gaugeSetoid X G) A.conn) = Quotient.mk _ B.conn :=
      Discrete.eq_of_hom f
    obtain ⟨g, hg⟩ := Quotient.exact h1
    exact ⟨⟨g, hg⟩, Subsingleton.elim _ _⟩
  · obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn with
    | h A => exact ⟨⟨A⟩, ⟨eqToIso rfl⟩⟩
  · by_contra hc
    push_neg at hc
    obtain ⟨hne, hns⟩ := hc
    obtain ⟨v⟩ := hne
    obtain ⟨a, ha⟩ := exists_ne (1 : G)
    let A : PotG X G := ⟨fun _ => 1⟩
    let f : A ⟶ A := ⟨fun _ => a, by funext e; simp [gaugeAct, A]⟩
    have hmap : (orbitF X G).map f = (orbitF X G).map (𝟙 A) := Subsingleton.elim _ _
    have hf := congrArg (fun k : A ⟶ A => k.1 v) ((orbitF X G).map_injective hmap)
    exact ha hf
  · apply Subtype.ext
    funext v
    rcases h with h | h
    · exact (h.false v).elim
    · exact Subsingleton.elim _ _

end GaugeFunctor

open GaugeFunctor CategoryTheory in
theorem solution (X : Graph) (G : Type) [Group G] :
    (orbitF X G).Full ∧ (orbitF X G).EssSurj ∧
      ((orbitF X G).Faithful ↔ (IsEmpty (Fin X.nV) ∨ Subsingleton G)) :=
  ofs_main X G
