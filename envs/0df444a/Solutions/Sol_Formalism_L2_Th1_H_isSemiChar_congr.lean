-- Prove2me | solution 1 for Formalism.L2.Th1.H.isSemiChar_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:49.813471+00:00
-- url     : https://prove2.me/submissions/ef604d14-d82f-4848-b90c-30ec5dfeeb41

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb

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
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (α β : V → ℂ) (hab : ∀ x ∈ Λ, α x = β x) (hβ : IsSemiChar H Λ β) : IsSemiChar H Λ α := by
  refine ⟨fun x hx => by rw [hab x hx]; exact hβ.1 x hx, fun x hx y hy => ?_⟩
  rw [hab x hx, hab y hy, hab _ (Λ.add_mem hx hy)]
  exact hβ.2 x hx y hy
end Formalism.L2.Th1.H
