-- Prove2me | solution 1 for Formalism.L2.Th1.H.out_mk_latA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:50.521147+00:00
-- url     : https://prove2.me/submissions/6409c8d9-e259-4aa2-95e8-ad3cd04c8402

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (x : Λ) : ∃ k ∈ latA Λ δ Ae,
    ((Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : Λ) : V)
      = (x : V) + k := by
  have e : -(Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ)) + x ∈
      (latA Λ δ Ae).addSubgroupOf Λ := by
    first
    | (rw [← QuotientAddGroup.eq]; exact Quotient.out_eq _)
    | exact (QuotientAddGroup.eq).mp (Quotient.out_eq (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ))
    | (rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq'])
  refine ⟨-(((-(Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ)) + x : Λ)) : V),
    ?_, ?_⟩
  · exact (latA Λ δ Ae).neg_mem (AddSubgroup.mem_addSubgroupOf.mp e)
  · push_cast
    abel
end Formalism.L2.Th1.H
