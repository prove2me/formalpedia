-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.finrank_comap_mkQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:26.843018+00:00
-- url     : https://prove2.me/submissions/618d5cf2-7730-490a-a535-594ccf6224ff

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
attribute [local instance] finite_quot
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (A : Submodule F W) (V : Submodule F (W ⧸ A)) :
    Module.finrank F (V.comap A.mkQ) = Module.finrank F V + Module.finrank F A := by
  haveI : Module.Finite F (V.comap A.mkQ) := Module.Finite.of_finite
  let f : (V.comap A.mkQ) →ₗ[F] V := A.mkQ.restrict (fun x hx => hx)
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective A v
    exact ⟨⟨w, hv⟩, rfl⟩
  have hker : (LinearMap.ker f).map (V.comap A.mkQ).subtype = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h0 : A.mkQ (y : W) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      exact (Submodule.Quotient.mk_eq_zero A).mp h0
    · intro hx
      have hmk : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).mpr hx
      have hxU : x ∈ V.comap A.mkQ := by
        show A.mkQ x ∈ V
        rw [hmk]; exact V.zero_mem
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      show f ⟨x, hxU⟩ = 0
      exact Subtype.ext hmk
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
  have h2 : Module.finrank F (LinearMap.ker f) = Module.finrank F A :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (V.comap A.mkQ).subtype
      (Submodule.injective_subtype _) (LinearMap.ker f))).trans
      (LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hker))
  omega
end Formalism.G0.TypeIIUpP
