-- Prove2me | solution 1 for Formalism.REAL.polarLog_mem_hermitian_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:55.906626+00:00
-- url     : https://prove2.me/submissions/223d8f73-59d7-4b2e-89ec-2c4db0756e1c

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_polar_log_hermitian
import Theorems.Thm_Formalism_REAL_polar_log_anticommutes_signature
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
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inP ε (polarLog g) := by
  have hJ := polar_log_anticommutes_signature hg
  have h2 : polarLog g * Jm ε = -(Jm ε * polarLog g) := by
    calc polarLog g * Jm ε = Jm ε * (Jm ε * polarLog g * Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Jm_mul_Jm_eq_one, one_mul]
      _ = -(Jm ε * polarLog g) := by rw [hJ, mul_neg]
  refine ⟨?_, h2⟩
  unfold inG
  rw [polar_log_hermitian, h2, neg_add_cancel]
end Formalism.REAL
