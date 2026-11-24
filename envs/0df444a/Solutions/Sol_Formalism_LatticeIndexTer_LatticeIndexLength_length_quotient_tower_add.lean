-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.length_quotient_tower_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:25.50194+00:00
-- url     : https://prove2.me/submissions/f02d9720-1263-420c-9633-8892b19825bd

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (D E P : Submodule O X) (hDE : D ≤ E) (hEP : E ≤ P) :
    Module.length O (P ⧸ D.comap P.subtype) =
      Module.length O (E ⧸ D.comap E.subtype) + Module.length O (P ⧸ E.comap P.subtype) := by
  let f : (E ⧸ D.comap E.subtype) →ₗ[O] (P ⧸ D.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hEP) (by intro x hx; simpa using hx)
  let g : (P ⧸ D.comap P.subtype) →ₗ[O] (P ⧸ E.comap P.subtype) :=
    Submodule.factor (Submodule.comap_mono hDE)
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H e => ?_
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  · exact Submodule.factor_surjective _
  · intro y
    induction y using Submodule.Quotient.induction_on with | H p => ?_
    rw [show g (Submodule.Quotient.mk p) = Submodule.Quotient.mk p from Submodule.factor_mk _ p,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hp
      exact ⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | H e => ?_
      simp only [f, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.eq, Submodule.mem_comap] at hx
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion] at hx
      have : (p : X) = (e : X) - ((e : X) - p) := by abel
      rw [this]
      exact E.sub_mem e.2 (hDE hx)
end Formalism.LatticeIndexTer.LatticeIndexLength
