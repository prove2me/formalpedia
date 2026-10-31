-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_39
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:13:14.259716+00:00
-- url     : https://prove2.me/submissions/871dca8a-a358-4f28-a496-ac4f1088570b

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits ConcreteSheaves.Quasitopos Opposite

universe u
variable {D : Type u} [SmallCategory D]

namespace CS39Aux

lemma isSheafCov_iff (K : Coverage D) (P : Dᵒᵖ ⥤ Type u) :
    IsSheafCov K P ↔ Presheaf.IsSheaf K.toGrothendieck P := by
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  rfl

lemma isConcrete_of_isLimit {T : D} {J : Type u} [SmallCategory J] (F : J ⥤ Dᵒᵖ ⥤ Type u)
    (c : Cone F) (hc : IsLimit c) (hF : ∀ j, IsConcrete T (F.obj j)) :
    IsConcrete T c.pt := by
  intro E φ ψ h
  apply yonedaEquiv.symm.injective
  apply hc.hom_ext
  intro j
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply hF j E
  funext d
  have := congrFun h d
  show (F.obj j).map d.op ((c.π.app j).app (op E) φ) = (F.obj j).map d.op ((c.π.app j).app (op E) ψ)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact congrArg _ this

instance closed (K : Coverage D) (T : D) (J : Type u) [SmallCategory J] :
    (IsDSpace K T).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    have hd := h.prop_diag_obj
    refine ⟨?_, ?_⟩
    · rw [isSheafCov_iff]
      let G : J ⥤ Sheaf K.toGrothendieck (Type u) :=
        ObjectProperty.lift _ h.diag (fun j => (isSheafCov_iff K _).1 (hd j).1)
      exact Sheaf.isSheaf_of_isLimit G _ h.isLimit
    · exact isConcrete_of_isLimit _ _ h.isLimit (fun j => (hd j).2)

end CS39Aux

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    HasLimits (DSpace K T) ∧ PreservesLimits (IsDSpace K T).ι := by
  have : ∀ (J : Type u) [SmallCategory J], (IsDSpace K T).IsClosedUnderLimitsOfShape J :=
    fun J _ => CS39Aux.closed K T J
  refine ⟨⟨fun J _ => inferInstance⟩, ⟨fun {J} _ => inferInstance⟩⟩
