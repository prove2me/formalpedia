-- Prove2me | solution 1 for Formalism.L2.Th1.H.relIdx_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:19.466345+00:00
-- url     : https://prove2.me/submissions/fd84de57-bc20-4f8b-a4fd-777657caf414

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (Λ₁ Λ₂ : AddSubgroup V) {x : V} (hx : x ∈ Λ₂) :
    (relIdx Λ₁ Λ₂ : ℂ) • x ∈ Λ₁ := by
  have h := AddSubgroup.nsmul_index_mem (Λ₁.addSubgroupOf Λ₂) ⟨x, hx⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h
  unfold relIdx
  rw [Nat.cast_smul_eq_nsmul]
  simpa [AddSubgroup.relIndex] using h
end Formalism.L2.Th1.H
