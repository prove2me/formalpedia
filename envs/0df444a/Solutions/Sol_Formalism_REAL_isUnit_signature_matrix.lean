-- Prove2me | solution 1 for Formalism.REAL.isUnit_signature_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:49.185469+00:00
-- url     : https://prove2.me/submissions/0a697afe-6ec5-4889-9b2d-3b5523738cd2

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Formalism.REAL
variable {n : ℕ}
private lemma Jm_mul_Jm_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_Jm_eq_one ε, Jm_mul_Jm_eq_one ε⟩, rfl⟩
end Formalism.REAL
