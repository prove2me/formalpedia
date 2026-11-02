-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.lemma_49
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:43:15.050274+00:00
-- url     : https://prove2.me/submissions/d35d8911-65e4-4ede-a917-e1db8ecb29a4

import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos
open GrothendieckTopology

universe u
variable {D : Type u} [SmallCategory D]

namespace CS49Aux

lemma points_mem (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {X : D} (S : Sieve X)
    (hS : S ∈ K.toGrothendieck X) (x : T ⟶ X) : S x := by
  induction hS with
  | of X R hR =>
    obtain ⟨Y, f, hf, y, rfl⟩ := hK.jointlySurj R hR x
    exact (Sieve.generate R).downward_closed (Sieve.le_generate R _ _ hf) y
  | top X => trivial
  | transitive X R S hR hS ihR ihS =>
    have h := ihS (ihR x) (𝟙 T)
    simpa using h

lemma separated (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) (hP : IsConcrete T P)
    (X : D) (S : K.toGrothendieck.Cover X) (x y : P.obj (op X))
    (h : ∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) : x = y := by
  apply hP X
  funext d
  exact h ⟨T, d, points_mem K T hT hK S.1 S.2 d⟩

end CS49Aux

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) (hP : IsConcrete T P) :
    IsDSpace K T ((K.toGrothendieck).plusObj P) := by
  have hsep := CS49Aux.separated K T hT hK P hP
  have hinj := Plus.inj_of_sep P hsep
  refine ⟨?_, ?_⟩
  · have hs := Plus.isSheaf_of_sep P hsep
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage] at hs
    intro X R hR
    exact hs R hR
  · intro X a b hab
    obtain ⟨S, x, rfl⟩ := Plus.exists_rep (J := K.toGrothendieck) (P := P) a
    obtain ⟨R, y, rfl⟩ := Plus.exists_rep (J := K.toGrothendieck) (P := P) b
    apply (Plus.eq_mk_iff_exists x y).2
    refine ⟨S ⊓ R, homOfLE inf_le_left, homOfLE inf_le_right, ?_⟩
    apply Meq.ext
    intro I
    change x ⟨I.Y, I.f, I.hf.1⟩ = y ⟨I.Y, I.f, I.hf.2⟩
    apply hP I.Y
    funext d
    apply hinj T
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    erw [Plus.toPlus_apply S x ⟨I.Y, I.f, I.hf.1⟩,
      Plus.toPlus_apply R y ⟨I.Y, I.f, I.hf.2⟩]
    simpa only [← FunctorToTypes.map_comp_apply, ← op_comp] using congrFun hab (d ≫ I.f)
