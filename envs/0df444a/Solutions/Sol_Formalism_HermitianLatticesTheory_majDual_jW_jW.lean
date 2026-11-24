-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_jW_jW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:54.431807+00:00
-- url     : https://prove2.me/submissions/701e7b9b-cf29-4637-aa68-d9c8414bd22d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_sgn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsFrame h b v (X v))
    (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) : jW h b X (jW h b X u) = u := by
  ext p
  rw [majDual_jW_apply, majDual_jW_apply, ← mul_assoc]
  rcases (majDual_sgn h b X hX p.1).2 p.2.1 with hs | hs <;> simp [hs]
end Formalism.HermitianLatticesTheory
