-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.Hom.bijective_map_and_forall_map_eq_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/98d9f65a-40d4-5171-ad73-750fe34b1231

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso

set_option autoImplicit false

universe u

noncomputable section

namespace P2mIsoHomGraded

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem toLawHom_comp {X Y Z : FormalODModule p B} (g : Y.Hom Z) (f : X.Hom Y) :
    (g.comp f).toLawHom = g.toLawHom.comp f.toLawHom :=
  MvFormalGroup.Hom.ext (funext fun _ => rfl)

theorem toLawHom_id (X : FormalODModule p B) : (FormalODModule.Hom.id X).toLawHom = MvFormalGroup.Hom.id X.F :=
  MvFormalGroup.Hom.ext (funext fun _ => rfl)

theorem toLawHom_comp_varpiEnd {X Y : FormalODModule p B} (u : Y.Hom X) :
    u.toLawHom.comp Y.varpiEnd = (X.varpiEnd : MvFormalGroup.Hom X.F X.F).comp u.toLawHom :=
  MvFormalGroup.Hom.ext (funext fun i => congrFun u.isODHom.2.2 i)

theorem toLawHom_comp_actEnd {X Y : FormalODModule p B} (u : Y.Hom X) (a : Zp2 p) :
    u.toLawHom.comp (Y.actEnd a) = (X.actEnd a : MvFormalGroup.Hom X.F X.F).comp u.toLawHom :=
  MvFormalGroup.Hom.ext (funext fun i => congrFun (u.isODHom.2.1 a) i)

end P2mIsoHomGraded

end

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule P2mIsoHomGraded in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (Y X : CerednikDrinfeld.FormalODModule p B) (u : Y.Hom X) (hu : u.IsIso)
    (g : MvFormalGroup.CartierModule p Y.F →+ MvFormalGroup.CartierModule p X.F)
    (hg : g = MvFormalGroup.CartierModule.map u.toLawHom) :
    Function.Bijective g ∧
    (∀ (w : WittVector p B) (m : MvFormalGroup.CartierModule p Y.F),
      g (w • m) = w • g m) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.frobenius m) =
        MvFormalGroup.CartierModule.frobenius (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.verschiebungInt m) =
        MvFormalGroup.CartierModule.verschiebungInt (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.endAct Y.varpiEnd m) =
        MvFormalGroup.CartierModule.endAct X.varpiEnd (g m)) ∧
    (∀ (i : ℕ) (m : MvFormalGroup.CartierModule p Y.F),
      m ∈ Y.gradedPiece j i → g m ∈ X.gradedPiece j i) := by
  subst hg
  obtain ⟨v, hvu, huv⟩ := hu
  have h1 : ∀ m : MvFormalGroup.CartierModule p Y.F, MvFormalGroup.CartierModule.map v.toLawHom (MvFormalGroup.CartierModule.map u.toLawHom m) = m := by
    intro m
    rw [← map_comp, ← toLawHom_comp, hvu, toLawHom_id, CartierModule.map_id]
  have h2 : ∀ m : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.map u.toLawHom (MvFormalGroup.CartierModule.map v.toLawHom m) = m := by
    intro m
    rw [← map_comp, ← toLawHom_comp, huv, toLawHom_id, CartierModule.map_id]
  refine ⟨Function.bijective_iff_has_inverse.mpr ⟨_, h1, h2⟩, fun w m => map_smul_witt _ w m,
    fun m => map_frobenius _ m, fun m => map_verschiebungInt _ m, fun m => ?_, fun i m hm => ?_⟩
  · show MvFormalGroup.CartierModule.map u.toLawHom (MvFormalGroup.CartierModule.map Y.varpiEnd m) =
      MvFormalGroup.CartierModule.map X.varpiEnd (MvFormalGroup.CartierModule.map u.toLawHom m)
    rw [← map_comp, ← map_comp, toLawHom_comp_varpiEnd]
  · intro c
    show MvFormalGroup.CartierModule.map (X.actEnd _) (MvFormalGroup.CartierModule.map u.toLawHom m) = _
    rw [← map_comp, ← toLawHom_comp_actEnd, map_comp]
    change MvFormalGroup.CartierModule.map u.toLawHom (endAct (Y.actEnd _) m) = _
    rw [hm c, map_homothety]

end S_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso (solution)
