-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.lemma_44
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:19:49.225514+00:00
-- url     : https://prove2.me/submissions/40caf270-e235-41fb-a691-47f968c6d1b5

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {X Y A : DSpace K T} (f : X ⟶ A) (g : Y ⟶ A)
    [HasPullback f g] [HasBinaryProduct X Y] :
    StrongMono (prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  refine RegularMono.strongMono
    { Z := A
      left := prod.fst ≫ f
      right := prod.snd ≫ g
      w := by rw [prod.lift_fst_assoc, prod.lift_snd_assoc, pullback.condition]
      isLimit := Fork.IsLimit.mk _
        (fun s => pullback.lift (s.ι ≫ prod.fst) (s.ι ≫ prod.snd)
          (by simpa using s.condition))
        (fun s => by
          apply prod.hom_ext
          · rw [Fork.ι_ofι, Category.assoc, prod.lift_fst, pullback.lift_fst]
          · rw [Fork.ι_ofι, Category.assoc, prod.lift_snd, pullback.lift_snd])
        (fun s m hm => by
          apply pullback.hom_ext
          · have := congrArg (· ≫ prod.fst) hm
            simp only [Fork.ofι_pt, Fork.ι_ofι] at this
            rw [Category.assoc, prod.lift_fst] at this
            rw [this, pullback.lift_fst]
          · have := congrArg (· ≫ prod.snd) hm
            simp only [Fork.ofι_pt, Fork.ι_ofι] at this
            rw [Category.assoc, prod.lift_snd] at this
            rw [this, pullback.lift_snd]) }
