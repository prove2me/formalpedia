-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_len_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:42.702019+00:00
-- url     : https://prove2.me/submissions/32d242aa-df4e-4285-8137-f940f804a618

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (N Mm P : Submodule R W) (hNM : N ≤ Mm) (hMP : Mm ≤ P) :
    Module.length R (↥P ⧸ N.comap P.subtype) =
      Module.length R (↥Mm ⧸ N.comap Mm.subtype) + Module.length R (↥P ⧸ Mm.comap P.subtype) := by
  let f : (↥Mm ⧸ N.comap Mm.subtype) →ₗ[R] (↥P ⧸ N.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hMP) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  let g : (↥P ⧸ N.comap P.subtype) →ₗ[R] (↥P ⧸ Mm.comap P.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hNM hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      dsimp only [f] at hy
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hy
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hy
        dsimp only [g] at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨x, hy⟩, rfl⟩
      · rintro ⟨w, hw⟩
        rw [← hw]
        induction w using Submodule.Quotient.induction_on with
        | H z =>
          dsimp only [f, g]
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
          exact z.2
end Formalism.HermitianLatticesTheory
