-- Prove2me | solution 1 for FrobMednykh.card_hom_surfaceGroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:48:28.322689+00:00
-- url     : https://prove2.me/submissions/7218fdce-7ad1-46f3-9950-2302524644ea

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_lift_rel {G : Type} [Group G] (g : ℕ) (f : Fin g × Bool → G) :
    FreeGroup.lift f (surfaceRelator g) = commProd (fun j => (f (j, false), f (j, true))) := by
  unfold surfaceRelator commProd
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  simp

theorem fm_card_hom (G : Type) [Group G] [Finite G] (g : ℕ) :
    Nat.card (SurfaceGroup g →* G) = commCount G g 1 := by
  unfold commCount
  apply Nat.card_congr
  exact {
    toFun := fun φ => ⟨fun j => (φ (PresentedGroup.of (j, false)), φ (PresentedGroup.of (j, true))), by
      rw [← fm_lift_rel g (fun a => φ (PresentedGroup.of a))]
      have h1 : (φ.comp (PresentedGroup.mk _)) = FreeGroup.lift (fun a => φ (PresentedGroup.of a)) := by
        ext a; simp [PresentedGroup.of]
      rw [← h1, MonoidHom.comp_apply]
      rw [PresentedGroup.one_of_mem (Set.mem_singleton _), map_one]⟩
    invFun := fun x => PresentedGroup.toGroup
      (f := fun a : Fin g × Bool => if a.2 then (x.1 a.1).2 else (x.1 a.1).1) (by
        intro r hr
        rw [Set.mem_singleton_iff.mp hr, fm_lift_rel]
        simpa using x.2)
    left_inv := fun φ => by
      apply PresentedGroup.ext
      intro a
      rw [PresentedGroup.toGroup.of]
      rcases a with ⟨j, b⟩
      cases b <;> rfl
    right_inv := fun x => by
      apply Subtype.ext
      funext j
      simp [PresentedGroup.toGroup.of] }

theorem solution (G : Type) [Group G] [Finite G] (g : ℕ) :
    Nat.card (SurfaceGroup g →* G) = commCount G g 1 := by
  exact fm_card_hom G g


