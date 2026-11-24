-- Prove2me | solution 1 for Formalism.IncomingBounds.LatticeIndexAlt.qlen_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:37.023437+00:00
-- url     : https://prove2.me/submissions/c2135245-3a26-49c3-b6be-224b30e19012

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_map_comap_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.LatticeIndexAlt
open Formalism.LatticeIndexTer
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
namespace Formalism.IncomingBounds.LatticeIndexAlt
theorem _root_.solution (W : Submodule K X) (A B : Submodule O X) :
    qlen O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      qlen O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold qlen
  have hinj : Function.Injective ((W.subtype).restrictScalars O) := fun a b h => Subtype.ext h
  let e : ↥(A.comap ((W.subtype).restrictScalars O)) ≃ₗ[O] ↥(A ⊓ W.restrictScalars O) :=
    (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ (map_comap_sub W A))
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
  ext z
  rw [Submodule.mem_map_equiv]
  have key : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) = (z : X) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hzW : (z : X) ∈ W := (Submodule.mem_inf.mp z.2).2
  constructor
  · intro h
    have h' : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) ∈ B := h
    rw [key] at h'
    show (z : X) ∈ B ⊓ W.restrictScalars O
    exact Submodule.mem_inf.mpr ⟨h', hzW⟩
  · intro h
    have h2 : (z : X) ∈ B ⊓ W.restrictScalars O := h
    have h' : (z : X) ∈ B := (Submodule.mem_inf.mp h2).1
    rw [← key] at h'
    exact h'
end Formalism.IncomingBounds.LatticeIndexAlt
