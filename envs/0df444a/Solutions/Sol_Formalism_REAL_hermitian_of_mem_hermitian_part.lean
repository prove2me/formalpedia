-- Prove2me | solution 1 for Formalism.REAL.hermitian_of_mem_hermitian_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:04.183312+00:00
-- url     : https://prove2.me/submissions/14e10352-a541-4772-ba6a-b41d629bb3bb

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
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨h1, h2⟩ := hX
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]
    exact eq_neg_of_add_eq_zero_left h1
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h3]
    _ = X := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
end Formalism.REAL
