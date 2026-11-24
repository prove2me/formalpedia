-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majBasic_majAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:52.827506+00:00
-- url     : https://prove2.me/submissions/5f8de9ef-ac01-44e4-a9ec-25ca23ea554a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = star (vecAt b v x) ⬝ᵥ ((((X v)⁻¹)ᴴ * (X v)⁻¹) *ᵥ vecAt b v y) := by
  unfold majAt
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl
end Formalism.HermitianLatticesTheory
