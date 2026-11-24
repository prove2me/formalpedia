-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.Ymat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:47.474846+00:00
-- url     : https://prove2.me/submissions/bd6f2f21-3b8d-4856-a059-14ef2b38d6b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RankUpdateMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
end Formalism.L2.S.L6.UnitaryStandardVectors
