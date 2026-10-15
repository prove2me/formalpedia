-- Prove2me | solution 1 for GaugeFunctor.not_faithful_of_toDiscrete
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-14T17:54:00.571029+00:00
-- url     : https://prove2.me/submissions/21697852-ae14-440d-879a-e4995fb409ea

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem nfd_main (X : Graph) (G : Type) [Group G] [Nontrivial G]
    (hV : Nonempty (Fin X.nV)) {α : Type*} (F : PotG X G ⥤ Discrete α) : ¬ F.Faithful := by
  intro hF
  obtain ⟨v⟩ := hV
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  let A : PotG X G := ⟨fun _ => 1⟩
  let f : A ⟶ A := ⟨fun _ => a, by funext e; simp [gaugeAct, A]⟩
  have hmap : F.map f = F.map (𝟙 A) := Subsingleton.elim _ _
  have hf := congrArg (fun k : A ⟶ A => k.1 v) (F.map_injective hmap)
  exact ha hf

end GaugeFunctor

open GaugeFunctor CategoryTheory in
theorem solution (X : Graph) (G : Type) [Group G] [Nontrivial G]
    (hV : Nonempty (Fin X.nV)) {α : Type*} (F : PotG X G ⥤ Discrete α) : ¬ F.Faithful :=
  nfd_main X G hV F
